#![feature(decl_macro)]
#![allow(unused)]
#![allow(non_snake_case)]
#![feature(hash_extract_if)]

use amplify_derive::From;
use anyhow::{anyhow, bail, Ok, Result};
use bimap::BiMap;

use derivative::Derivative;
use fixedbitset::FixedBitSet;

use rustsat::{
    clause,
    encodings::{card, pb},
    instances::{BasicVarManager, ManageVars, Objective, SatInstance},
    types::Clause,
    types::{Lit, TernaryVal, Var},
};
use scuttle::{KernelFunctions, Limits, Options, PMinimal, Solve};
use std::{
    any::TypeId,
    collections::{hash_map::Entry, HashMap, HashSet},
    fmt::Debug,
    future::{self, Future},
    hash::Hash,
    marker::PhantomData,
    ops::Index,
    pin::Pin,
};

use rustsat::instances::MultiOptInstance;

use daggy::{
    petgraph::{
        csr::Csr,
        graph::DefaultIx,
        visit::{
            EdgeRef, FilterNode, IntoEdges, IntoEdgesDirected, IntoNeighborsDirected,
            IntoNodeIdentifiers, NodeFiltered, NodeFilteredNodes, Reversed, Topo, VisitMap,
            Visitable,
        },
    },
    stable_dag::StableDag,
    walker::{Filter, Peekable, Recursive, Skip},
    Dag, NodeIndex, Walker,
};

pub trait Mergeable {
    fn merge(&mut self, Δ: Self) -> Result<()>;
}

/// Read or Write
pub enum ReqType {
    R,
    W,
}

pub type SATVar = usize;

#[derive(Debug, Clone, PartialEq, Eq, From, Hash)]
pub struct RsrcKey<K: Key>(pub TypeId, pub K);

pub trait Key: Hash + Eq + Debug + Clone {}
/// Subject key
pub trait SKey: Key {}
/// Task key, uniquely identifies a task within the scope of a subject
pub trait TKey: Key {}

pub struct FnPlan<'SharedState, SK: Key, TK: Key, K: Key, GS, E, S: Clone> {
    /// Identifies the subject it belongs to
    pub subject: SK,
    /// Set it to () if you don't need it.
    pub tkey: TK,
    /// Demands for resources
    pub req: HashMap<RsrcKey<K>, ReqType>,
    /// Option because we will move it out when executing
    pub exec: Option<
        Box<
            dyn FnOnce(&'SharedState GS) -> Pin<Box<dyn Future<Output = Result<E>> + 'SharedState>>
                + 'SharedState,
        >,
    >,
    /// State change that would be caused if the plan gets executed
    pub result: S,
}

impl<K: Key> Mergeable for HashMap<RsrcKey<K>, ReqType> {
    fn merge(&mut self, Δ: Self) -> Result<()> {
        for (k, v) in Δ {
            match self.entry(k) {
                Entry::Occupied(mut o) => {
                    o.get_mut().merge(v)?;
                }
                Entry::Vacant(va) => {
                    va.insert(v);
                }
            }
        }
        Ok(())
    }
}

impl Mergeable for ReqType {
    fn merge(&mut self, Δ: Self) -> Result<()> {
        match self {
            ReqType::R => *self = Δ,
            ReqType::W => (),
        }
        Ok(())
    }
}

pub trait ScheSubject {
    /// Label-like small state
    type S: NodeStatusT;
    /// State changes a FnPlan can return. Effect
    type E;
    /// Global state, immutable
    type GS;
    /// Resource key
    type RKey: Key;
    /// Subject key
    type SK: SKey;
    /// Task key
    type TK: TKey;
    /// the task causes a status change
    fn next_task<'f>(
        &'f self,
        status: Self::S,
    ) -> Vec<FnPlan<'f, Self::SK, Self::TK, Self::RKey, Self::GS, Self::E, Self::S>>;
    fn subject_key(&self) -> &Self::SK;
    fn initial_status(&self) -> Self::S;
    fn destroy(
        &self,
        status: Self::S,
    ) -> FnPlan<'_, Self::SK, Self::TK, Self::RKey, Self::GS, Self::E, Self::S>;
}

pub trait NodeStatusT: Clone + Debug {
    fn node_status(&self) -> NodeStatus;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NodeStatus {
    Done,
    Undone,
}

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct AsyncScheduler<S: NodeStatusT, E, GS, RKey: Key, SK: SKey, TK: TKey> {
    /// Wait-for graph. A --depend---> B
    dag: StableDag<Box<dyn ScheSubject<S = S, E = E, GS = GS, RKey = RKey, SK = SK, TK = TK>>, ()>,
    keys: BiMap<SK, NodeIndex>,
    state: HashMap<SK, S>,
    /// Done nodes have status of done.
    /// At the moment of find_runnable, they can be depended on
    done: HashSet<NodeIndex>,
    /// All (runnable && worth running) nodes
    ready: HashSet<NodeIndex>,
    /// Nodes pending for traversal. They will be traversed each find_runnable, and removed from this set.
    pending: HashSet<NodeIndex>,
    /// Removal is a special operation
    removing: HashSet<NodeIndex>,
}

impl<S: NodeStatusT, E, GS, RKey: Key, SK: SKey, TK: TKey> AsyncScheduler<S, E, GS, RKey, SK, TK> {
    pub async fn upkeep_concurrent<'this: 'f, 'f>(
        &'this mut self,
        immutable: &'f GS,
    ) -> Result<Vec<(Result<E>, FnPlan<'f, SK, TK, RKey, GS, E, S>)>> {
        self.find_runnable_subjects();
        if self.ready.is_empty() {
            return Ok(vec![]);
        }

        let mut sat: SatInstance<BasicVarManager> = SatInstance::new();
        let mut tasks: HashMap<Var, (FnPlan<SK, TK, RKey, GS, E, S>, NodeIndex)> =
            Default::default(); // whether enable a task
        let mut rsrcs: BiMap<Var, RsrcKey<RKey>> = Default::default(); // whether enable a resource
        let mut reads: BiMap<Var, RsrcKey<RKey>> = Default::default(); // whether read a resource
        let mut reader: HashMap<Var, Vec<Var>> = Default::default(); // Read_var to readers
        let mut writer: HashMap<Var, Vec<Var>> = Default::default(); // Resource to writers

        let mut process_plan = |fp, ni: NodeIndex| {
            let tv = sat.var_manager().new_var();
            tasks.insert(tv, (fp, ni));
            let (fp, n) = tasks.get(&tv).unwrap();
            for (rs, access) in &fp.req {
                if !rsrcs.contains_right(&rs) {
                    let rv = sat.var_manager().new_var();
                    rsrcs.insert(rv, rs.to_owned());
                    writer.insert(rv, vec![]);
                    let rv = sat.var_manager().new_var();
                    reads.insert(rv, rs.to_owned());
                    reader.insert(rv, vec![]);
                }
                let resv = rsrcs.get_by_right(&rs).unwrap();
                let readv = reads.get_by_right(&rs).unwrap();
                match access {
                    ReqType::R => {
                        reader.get_mut(readv).unwrap().push(tv);
                    }
                    ReqType::W => {
                        writer.get_mut(resv).unwrap().push(tv);
                    }
                }
            }
        };

        let m = self.ready.difference(&self.done);
        for (sj, ni) in m.map(|x| (&self.dag[*x], x)) {
            let fnplan = sj.next_task(
                self.state
                    .get(sj.subject_key())
                    .map(|k| k.to_owned())
                    .unwrap_or(sj.initial_status()),
            );
            for fp in fnplan {
                process_plan(fp, *ni);
            }
        }
        let m = &self.removing;
        for (sj, ni) in m.iter().map(|x| (&self.dag[*x], x)) {
            let fnplan = sj.destroy(
                self.state
                    .get(sj.subject_key())
                    .map(|k| k.to_owned())
                    .unwrap_or(sj.initial_status()),
            );
            process_plan(fnplan, *ni);
        }
        if tasks.len() == 0 {
            return Ok(vec![]);
        }
        for (rv, readers) in reader {
            let rders: Vec<_> = readers.iter().map(|x| x.pos_lit()).collect();
            for tv in rders.iter() {
                // A reader enabled => Read
                sat.add_lit_impl_lit(*tv, rv.pos_lit());
            }
            // Read => One or more readers are enabled
            sat.add_lit_impl_clause(rv.pos_lit(), rders);
        }
        for (rv, writers) in writer {
            let mut users: Vec<_> = writers.iter().map(|x| x.pos_lit()).collect();
            let rskey = rsrcs.get_by_left(&rv).unwrap();
            let readv = reads.get_by_right(rskey).unwrap();
            users.push(readv.pos_lit());
            // Either Read, WriteA or WriteB
            impl_at_most_one(rv.pos_lit(), &users, &mut sat);
            // Read || WriteByA || WriteByB ==> ResourceEnabled
            sat.add_clause_impl_lit(users, rv.pos_lit());
        }

        let minimized = tasks.keys().map(|v| (v.neg_lit(), 1usize));
        let o: Objective = minimized.into_iter().collect();
        let mo = MultiOptInstance::compose(sat, vec![o]);
        let mut solver: PMinimal<
            pb::DefIncUpperBounding,
            card::DefIncUpperBounding,
            BasicVarManager,
            fn(rustsat::types::Assignment) -> Clause,
            rustsat_minisat::core::Minisat,
        > = PMinimal::new_defaults(mo, Options::default()).unwrap();
        solver.solve(Limits::none()).unwrap();

        let pareto_front = solver.pareto_front();
        let sol = pareto_front
            .into_iter()
            .next()
            .ok_or(AllocationError)?
            .into_iter()
            .next()
            .ok_or(AllocationError)?;

        let (exe, wait): (HashMap<_, _>, _) =
            tasks
                .into_iter()
                .partition(|(k, v)| match sol.var_value(*k) {
                    TernaryVal::True | TernaryVal::DontCare => true,
                    _ => false,
                });

        let k = futures::future::join_all(exe.into_iter().map(|(v, (mut fp, ni))| async move {
            ((fp.exec.take().unwrap())(immutable).await, fp, ni)
        }))
        .await;

        for (r, fp, ni) in &k {
            if r.is_ok() {
                if fp.result.node_status() == NodeStatus::Done {
                    self.done.insert(*ni);
                }
                self.state
                    .insert(fp.subject.to_owned(), fp.result.to_owned());
            } else {
                // State transition failed. Keep previous state.
                self.ready.remove(ni);
            }
        }

        Ok(k.into_iter().map(|(r, f, i)| (r, f)).collect())
    }
    /// Errors if subjects would form wait-for loops
    pub fn add(
        &mut self,
        subject: Box<dyn ScheSubject<S = S, TK = TK, E = E, GS = GS, RKey = RKey, SK = SK>>,
        deps: &[SK],
    ) -> Result<()> {
        let sk = subject.subject_key().to_owned();
        debug_assert!(subject.initial_status().node_status() == NodeStatus::Undone);
        if self.keys.contains_left(&sk) {
            bail!("repeated adding")
        }

        let ni = self.dag.add_node(subject);
        self.keys.insert(sk, ni);
        let mut pass = false;

        for k in deps.into_iter().map(|k| {
            self.keys.get_by_left(k).ok_or(anyhow!(
                "Trying to add a subject with non-existent dependency"
            ))
        }) {
            let dp = *k?;

            self.dag.add_edge(ni, dp, ())?;
            if !self.done.contains(&dp) {
                pass = true;
            }
        }
        // at least one undone node ==> do not add to pending
        // In a static graph, all undone nodes can be visited from current pending nodes, by continue find_runnable
        // If I add any node to depend on them, it will be visited too.

        if !pass {
            self.pending.insert(ni);
        }

        Ok(())
    }
    fn find_runnable_subjects(&mut self) {
        // newfound runnable nodes, either source nodes, or extracted from pending.
        let traverse: HashSet<NodeIndex> = if self.done.is_empty() {
            NodeFiltered::from_fn(&self.dag, |ni| {
                // Parent --> Children/dependencies
                self.dag.children(ni).iter(&self.dag).next().is_none()
                    && !self.removing.contains(&ni)
            })
            .node_identifiers()
            .collect()
        } else {
            self.pending
                .extract_if(|node| {
                    // Get all executable subjects, and remove them from pending
                    self.dag
                        .children(*node)
                        .iter(&self.dag)
                        .fold(true, |acc, (_e, dep)| {
                            acc && self.done.contains(&dep) && !self.removing.contains(&dep)
                        })
                })
                .collect()
        };
        // add the dependents to pending.
        for n in traverse.iter() {
            for (e, p) in self.dag.parents(*n).iter(&self.dag) {
                if !self.removing.contains(&p) {
                    self.pending.insert(p);
                }
            }
        }
        self.ready.extend(traverse);
    }
    pub fn debug(&self) {
        for (sk, ni) in &self.keys {
            let s = &self.state.get(sk);
            println!(
                "Subject {:?}, {:?}, {:?}",
                sk,
                s,
                s.map(|x| x.node_status()).unwrap_or(NodeStatus::Undone)
            );
        }
    }
    pub fn remove(&mut self, sk: &SK) -> Result<()> {
        let ni = self
            .keys
            .get_by_left(sk)
            .ok_or_else(|| anyhow!("given subject doesn't exist"))?;
        self.recur_remove(*ni);
        Ok(())
    }
    /// Mark it and all its dependencies as removing
    fn recur_remove(&mut self, n: NodeIndex) {
        while let Some((ei, ni)) = self.dag.parents(n).walk_next(&self.dag) {
            self.ready.remove(&ni);
            self.pending.remove(&ni);
            self.removing.insert(ni);
            self.recur_remove(ni);
        }
    }
}

/// X ==> (at_most_1 A B C)
fn impl_at_most_one(pre: Lit, list: &[Lit], sat: &mut SatInstance) {
    let mut k = 0;
    while k < list.len() {
        let mut p = k + 1;
        while p < list.len() {
            let cl = clause!(-pre, -list[k], -list[p]);
            sat.add_clause(cl);
            p += 1;
        }
        k += 1;
    }
}

use thiserror::{self, Error};

#[derive(Error, Debug)]
#[error("Maybe a programming error. SAT solver can not find a solution")]
pub struct AllocationError;

pub macro Demand {
    ( $($typ:ident/$k:expr => $access:ident),+ ) => (
        HashMap::from_iter([$(( RsrcKey(std::any::TypeId::of::<$typ>(),$k) , ReqType::$access)),+])
    )
}

pub macro rkey( $typ:ident/$k:expr ) {
    RsrcKey(std::any::TypeId::of::<$typ>(), $k)
}

#[cfg(test)]
pub mod test;

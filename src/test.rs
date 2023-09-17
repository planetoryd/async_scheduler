use crate::*;
use amplify_derive::*;
use dashmap::DashMap;

impl Key for u8 {}
impl SKey for u8 {}
impl TKey for u8 {}

struct ExampleSubject {
    /// Key should be something small, low-cost.
    subject_key: u8,
}

#[derive(Default)]
/// Will be passed to tasks as a &SharedState (shared reference)
struct SharedState {
    shared: String,
    ra: DashMap<u8, ResourceA>,
    rb: DashMap<u8, ResourceB>,
}

#[derive(From)]
struct ResourceA(u8);

#[derive(From)]
struct ResourceB(u8);

impl ScheSubject for ExampleSubject {
    type RKey = u8;
    type E = ();
    type GS = SharedState;
    type S = Stages;
    type SK = u8;
    type TK = u8;
    fn initial_status(&self) -> Self::S {
        Stages::Prepare
    }
    fn subject_key(&self) -> &Self::SK {
        &self.subject_key
    }
    fn next_task<'f>(
        &'f self,
        status: Self::S,
    ) -> Vec<FnPlan<'f, Self::SK, Self::TK, Self::RKey, Self::GS, Self::E, Self::S>> {
        match status {
            Stages::Prepare => [
                match self.subject_key {
                    0 => fnp!(
                        Demand!(ResourceA/1 => W, ResourceB/1 => W),
                        Alpha,
                        self,
                        status
                    ),
                    1 => fnp!(Demand!(ResourceA/1 => R), Alpha, self, status),
                    2 | _ => fnp!(Demand!(ResourceA/3 => R), Alpha, self, status),
                },
                match self.subject_key {
                    0 => fnp!(Demand!(ResourceB/1 => R), Alpha, self, status),
                    1 => fnp!(Demand!(ResourceA/1 => R), Alpha, self, status),
                    2 | _ => fnp!(Demand!(ResourceA/6 => R), Alpha, self, status),
                },
            ]
            .into(),
            Stages::Alpha => [fnp!(Demand!(ResourceA/1 => R), Beta, self, status)].into(),
            _ => [].into(),
        }
    }
    fn destroy(
        &self,
        status: Self::S,
    ) -> FnPlan<'_, Self::SK, Self::TK, Self::RKey, Self::GS, Self::E, Self::S> {
        fnp!(Demand!(ResourceA/2 => W), Suspended, self, status)
    }
}

#[derive(Clone, Debug, Copy)]
enum Stages {
    Prepare,
    Alpha,
    Beta,
    Suspended,
}

impl NodeStatusT for Stages {
    fn node_status(&self) -> NodeStatus {
        match &self {
            Self::Prepare | Self::Alpha => NodeStatus::Undone,
            _ => NodeStatus::Done,
        }
    }
}

pub macro fnp( $r:expr, $sta:ident, $obj:ident, $status:ident ) {
    FnPlan {
        tkey: 0,
        subject: $obj.subject_key,
        req: $r,
        exec: Some(Box::new(move |shared: &Self::GS| {
            Box::pin(async move {
                println!("Subject {:?} from {:?}", $obj.subject_key, $status);
                Ok(())
            })
        })),
        result: Stages::$sta,
    }
}

#[async_std::test]
pub async fn simple() -> Result<()> {
    let mut sche = AsyncScheduler::default();
    let mut global = SharedState::default();
    global.ra.extend([(1, 0.into()), (2, 0.into())]);
    global.rb.extend([(1, 0.into()), (2, 0.into())]);
    sche.add(Box::new(ExampleSubject { subject_key: 0 }), &[])?;
    let k = sche.add(Box::new(ExampleSubject { subject_key: 1 }), &[1]);
    assert!(k.is_err());
    sche.add(Box::new(ExampleSubject { subject_key: 1 }), &[0]);
    sche.upkeep_concurrent(&global).await?;
    sche.upkeep_concurrent(&global).await?;
    sche.add(Box::new(ExampleSubject { subject_key: 2 }), &[])?;
    for x in 1..10 {
        let k = sche.upkeep_concurrent(&global).await?;
        if k.len() == 0 {
            break;
        }
    }
    sche.debug();
    sche.add(Box::new(ExampleSubject { subject_key: 3 }), &[2]);
    for x in 1..10 {
        let k = sche.upkeep_concurrent(&global).await?;
        if k.len() == 0 {
            break;
        }
    }
    sche.debug();

    Ok(())
}

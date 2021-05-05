use swipl::prelude::*;

fn main() -> PrologResult<()> {
    let activator = MainEngineActivator::new();
    let activation = activator.initialize().unwrap();
    let context: Context<_> = activation.into();

    let term = term! {context: hello(world)}?;

    context.call_once(pred!(writeq / 1), [&term])?;
    context.call_once(pred!(nl / 0), [])?;

    Ok(())
}

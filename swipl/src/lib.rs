pub mod consts;

pub mod atom;
pub mod functor;
pub mod module;
pub mod predicate;
pub mod term;

pub mod context;
pub mod engine;

#[cfg(test)]
mod tests {
    use crate::engine::*;
    #[test]
    fn it_works() {
        Engine::new();

        assert_eq!(2 + 2, 4);
    }
}

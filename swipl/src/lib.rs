pub mod atom;
pub mod consts;
pub mod context;
pub mod engine;
pub mod functor;
pub mod term;

#[cfg(test)]
mod tests {
    use crate::engine::*;
    #[test]
    fn it_works() {
        Engine::new();

        assert_eq!(2 + 2, 4);
    }
}

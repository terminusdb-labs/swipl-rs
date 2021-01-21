pub mod engine;
pub mod term;
pub mod context;

#[cfg(test)]
mod tests {
    use crate::engine::*;
    #[test]
    fn it_works() {
        Engine::new();

        assert_eq!(2 + 2, 4);
    }
}

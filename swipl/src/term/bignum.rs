//! Support for rug Integer and Rational using SWI-Prolog's GMP support.

use crate::fli;
use crate::term::*;
use crate::{term_getable, unifiable};
use rug::{Integer, Rational};

term_getable! {
    (Integer, "bigint", term) => {
        let mut i = Integer::new();
        let ptr = i.as_raw_mut();

        let result = unsafe {
            fli::PL_get_mpz(term.term_ptr(), std::mem::transmute(ptr))
        };
        if result != 0 {
            Some(i)
        }
        else {
            None
        }
    }
}

unifiable! {
    (self:&Integer, term) => {
        let ptr = self.as_raw();

        let result = unsafe {
            fli::PL_unify_mpz(term.term_ptr(), std::mem::transmute(ptr))
        };

        result != 0
    }
}

term_getable! {
    (Rational, "bigrat", term) => {
        eprintln!("hi");
        let mut r = Rational::new();
        let ptr = r.as_raw_mut();

        let result = unsafe {
            fli::PL_get_mpq(term.term_ptr(), std::mem::transmute(ptr))
        };
        if result != 0 {
            Some(r)
        }
        else {
            None
        }
    }
}

unifiable! {
    (self:&Rational, term) => {
        let ptr = self.as_raw();

        let result = unsafe {
            fli::PL_unify_mpq(term.term_ptr(), std::mem::transmute(ptr))
        };

        result != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::*;
    use std::str::FromStr;
    #[test]
    fn get_bigint() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let big_int_str = "1234123412341234123412341234123412341234";
        let term = context.term_from_string(big_int_str).unwrap();

        let expected = Integer::from_str(big_int_str).unwrap();
        let i: Integer = term.get().unwrap();
        assert_eq!(expected, i);
    }

    #[test]
    fn unify_bigint() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let big_int_str = "1234123412341234123412341234123412341234";
        let i = Integer::from_str(big_int_str).unwrap();

        let term = context.new_term_ref();
        term.unify(&i).unwrap();

        let s = context.string_from_term(&term).unwrap();

        assert_eq!(big_int_str, s);
    }

    #[test]
    fn get_bigrat() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        // we construct a big rational in swipl using the 'r' notation.
        // We use a prime denominator to ensure no unexpected normalizing happens.
        let big_numerator = "1234123412341234123412341234123412341234";
        let big_prime_str = "19131612631094571991039";
        let big_rat_prolog_string = format!("{big_numerator}r{big_prime_str}");
        let big_rat_div_string = format!("{big_numerator}/{big_prime_str}");
        let term = context.term_from_string(&big_rat_prolog_string).unwrap();

        let expected = Rational::from_str(&big_rat_div_string).unwrap();
        let i: Rational = term.get().unwrap();
        assert_eq!(expected, i);
    }

    #[test]
    fn unify_bigrat() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let big_numerator = "1234123412341234123412341234123412341234";
        let big_prime_str = "19131612631094571991039";
        let big_rat_prolog_string = format!("{big_numerator}r{big_prime_str}");
        let big_rat_div_string = format!("{big_numerator}/{big_prime_str}");
        let i = Rational::from_str(&big_rat_div_string).unwrap();

        let term = context.new_term_ref();
        term.unify(&i).unwrap();

        let s = context.string_from_term(&term).unwrap();

        assert_eq!(big_rat_prolog_string, s);
    }

    #[test]
    fn unify_unequal_bigrat_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let big_numerator = "1234123412341234123412341234123412341234";
        let big_prime_str = "19131612631094571991039";
        let big_rat_prolog_string = format!("{big_numerator}r{big_prime_str}");
        let big_rat_div_string = format!("{big_numerator}/{big_prime_str}");
        let i = Rational::from_str(&big_rat_div_string).unwrap();
        let i2: Rational = i.clone() + 1;

        let term = context.new_term_ref();
        term.unify(&i).unwrap();
        assert!(term.unify(&i2).unwrap_err().is_failure());

        let s = context.string_from_term(&term).unwrap();

        assert_eq!(big_rat_prolog_string, s);
    }
}

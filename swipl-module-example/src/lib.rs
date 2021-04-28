use swipl::atom::*;
use swipl::context::*;
use swipl::result::*;
use swipl::*;

predicates! {
    semidet fn unify_with_42(_context, term) {
        term.unify(42_u64)
    }

    semidet fn unify_with_negative_42(_context, term) {
        term.unify(-42_i64)
    }

    semidet fn term_is_42(_context, term) {
        let num: u64 = term.get::<u64>()?;

        into_prolog_result(num == 42)
    }

    semidet fn copy_number(_context, term1, term2) {
        let num: u64 = term1.get()?;
        term2.unify(num)
    }

    semidet fn term_is_flurps(context, term) {
        let val: Atom = term.get()?;

        into_prolog_result(val.name(context) == "flurps")
    }

    semidet fn add_two_numbers(_context, n1_term, n2_term, out_term) {
        let n1: u64 = n1_term.get()?;
        let n2: u64 = n2_term.get()?;

        let out = n1 + n2;

        out_term.unify(out)
    }

    semidet fn throw_a_thing(context) {
        let term = term!{context: error(moo, _)};
        context.raise_exception(&term)
    }

    semidet fn rusty_panic(_context) {
        todo!();
    }

    nondet fn decrement<u64>(context, start, cur) {
        setup => {
            let num = start.get()?;
            Ok(num)
        },
        call(num) => {
            cur.unify(*num)?;
            if *num == 0 {
                Ok(false)
            }
            else {
                *num -= 1;
                Ok(true)
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn install() {
    register_unify_with_42();
    register_unify_with_negative_42();
    register_term_is_42();
    register_term_is_flurps();
    register_copy_number();
    register_add_two_numbers();
    register_throw_a_thing();
    register_rusty_panic();
    register_decrement();
}
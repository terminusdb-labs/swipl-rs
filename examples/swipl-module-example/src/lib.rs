use swipl::prelude::*;

use std::cmp::Ordering;
use std::io::{self, Write};
use std::sync::Arc;

predicates! {
    semidet fn unify_with_foo(_context, term) {
        let atom = Atom::new("foo");
        term.unify(&atom)
    }

    nondet fn unify_with_bar_baz<Vec<&'static str>>(context, term) {
        setup => {
            Ok(Some(vec!["bar", "baz"]))
        },
        call(v) => {
            let next = v.pop().unwrap();
            let atom = Atom::new(next);
            term.unify(&atom)?;

            Ok(!v.is_empty())
        }
    }
}

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

    semidet fn term_is_flurps(_context, term) {
        let val: Atom = term.get()?;

        into_prolog_result(val.name() == "flurps")
    }

    semidet fn add_two_numbers(_context, n1_term, n2_term, out_term) {
        let n1: u64 = n1_term.get()?;
        let n2: u64 = n2_term.get()?;

        let out = n1 + n2;

        out_term.unify(out)
    }

    semidet fn throw_a_thing(context) {
        let term = term!{context: error(moo, _)}?;
        context.raise_exception(&term)
    }

    semidet fn rusty_panic(_context) {
        todo!();
    }

    nondet fn decrement<u64>(context, start, cur) {
        setup => {
            let num = start.get()?;
            Ok(Some(num))
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

    semidet fn unify_with_blob(_context, term, num_term) {
        let num: u64 = num_term.get()?;
        let arc = Arc::new(Moo { num });
        term.unify(&arc)
    }

    semidet fn moo_num(_context, moo_term, num_term) {
        let arc: Arc<Moo> = moo_term.get()?;
        num_term.unify(arc.num)
    }

    semidet fn unify_with_wrapped_blob(_context, term, num_term) {
        let num: u64 = num_term.get()?;
        let arc = Arc::new(Inner { num });
        term.unify(&MooMoo(arc))
    }

    semidet fn moomoo_num(_context, moo_term, num_term) {
        let wrapper: MooMoo = moo_term.get()?;
        num_term.unify(wrapper.num)
    }

    semidet fn stream_write_hello(context, stream_term) {
        let mut stream: WritablePrologStream = stream_term.get()?;

        context.try_or_die(write!(stream, "こんにちは! 🫡\n"))
    }
}

#[arc_blob("moo")]
struct Moo {
    num: u64,
}

impl ArcBlobImpl for Moo {
    fn compare(&self, other: &Self) -> Ordering {
        self.num.cmp(&other.num)
    }

    fn write(&self, stream: &mut PrologStream) -> io::Result<()> {
        write!(stream, "<moo {}>", self.num)
    }
}

wrapped_arc_blob!("moomoo", MooMoo, Inner);

impl WrappedArcBlobImpl for MooMoo {
    fn write(inner: &Inner, stream: &mut PrologStream) -> io::Result<()> {
        write!(stream, "<moomoo {}>", inner.num)
    }
}

struct Inner {
    num: u64,
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
    register_unify_with_blob();
    register_moo_num();
    register_unify_with_wrapped_blob();
    register_moomoo_num();

    register_unify_with_foo();
    register_unify_with_bar_baz();

    register_stream_write_hello();
}

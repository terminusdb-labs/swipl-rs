use swipl_info::*;

fn main() {
    let info = get_swipl_info();

    println!("{:#?}", info);
}

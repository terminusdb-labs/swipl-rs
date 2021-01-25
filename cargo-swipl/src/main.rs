use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use std::env;
use std::process::Command;
use swipl_info::*;

fn subcmd_test(subcommand: &ArgMatches) {
    let info = get_swipl_info();

    let library_location = format!("{}/{}", info.swi_home, info.pack_so_dir);

    let cargo = env::var("CARGO").unwrap_or("cargo".to_owned());
    let mut command = Command::new(cargo);
    let ld_library_path = env::var("LD_LIBRARY_PATH").unwrap_or("".to_owned());
    let ld_library_path = format!("{}:{}", ld_library_path, library_location);
    command.env("LD_LIBRARY_PATH", ld_library_path);

    command.arg("test");
    if let Some(m) = subcommand.values_of("cmd") {
        let args: Vec<_> = m.collect();
        command.args(args);
    }

    command.spawn().unwrap().wait().unwrap();
}

fn main() {
    let app = App::new("cargo-swipl")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommand(
            SubCommand::with_name("swipl")
                .setting(AppSettings::SubcommandRequiredElseHelp)
                .subcommand(
                    SubCommand::with_name("test")
                        .setting(AppSettings::TrailingVarArg)
                        .setting(AppSettings::AllowLeadingHyphen)
                        .about("run tests with swi-prolog added to the load path")
                        .arg(Arg::from_usage("<cmd>... 'commands to run'").required(false)),
                ),
        );

    let matches = app.get_matches();
    let matches = matches
        .subcommand_matches("swipl")
        .expect("expected swipl subcommand to be used");

    if let Some(matches) = matches.subcommand_matches("test") {
        subcmd_test(matches);
    } else {
        panic!("unknown subcommand");
    }
}

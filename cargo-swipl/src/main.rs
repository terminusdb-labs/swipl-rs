mod module;
use module::*;

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use std::env;
use std::process::Command;
use swipl_info::*;

fn subcmd(subcommand: &ArgMatches, cmd: &str) {
    let info = get_swipl_info();

    let cargo = env::var("CARGO").unwrap_or("cargo".to_owned());
    let mut command = Command::new(cargo);

    if cfg!(target_os = "windows") {
        let path = env::var("PATH").unwrap_or("".to_owned());
        let path = format!("{};{}", info.lib_dir, path);
        command.env("PATH", path);
    } else {
        let ld_library_path = env::var("LD_LIBRARY_PATH").unwrap_or("".to_owned());
        let ld_library_path = format!("{}:{}", info.lib_dir, ld_library_path);
        command.env("LD_LIBRARY_PATH", ld_library_path);
    }

    command.env("SWI_HOME_DIR", info.swi_home);

    command.arg(cmd);
    if let Some(m) = subcommand.values_of("cmd") {
        let args: Vec<_> = m.collect();
        command.args(args);
    }

    let exit_status = command.spawn().unwrap().wait().unwrap();

    if let Some(code) = exit_status.code() {
        std::process::exit(code);
    }
}

fn main() {
    let app = App::new("cargo-swipl")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommand(
            SubCommand::with_name("run")
                .setting(AppSettings::TrailingVarArg)
                .setting(AppSettings::AllowLeadingHyphen)
                .about("run binary with swi-prolog added to the load path")
                .arg(Arg::from_usage("<cmd>... 'commands to run'").required(false)),
        )
        .subcommand(
            SubCommand::with_name("test")
                .setting(AppSettings::TrailingVarArg)
                .setting(AppSettings::AllowLeadingHyphen)
                .about("run tests with swi-prolog added to the load path")
                .arg(Arg::from_usage("<cmd>... 'commands to run'").required(false)),
        )
        .subcommand(
            SubCommand::with_name("module")
                .setting(AppSettings::TrailingVarArg)
                .setting(AppSettings::AllowLeadingHyphen)
                .about("do module stuff")
                .arg(Arg::from_usage("<cmd>... 'commands to run'").required(false)),
        );

    // Drop extra `swipl` argument provided by `cargo`.
    let mut found_swipl = false;
    let args = env::args().filter(|x| {
        if found_swipl {
            true
        } else {
            found_swipl = x == "swipl";
            x != "swipl"
        }
    });

    let matches = app.get_matches_from(args);

    if let Some(matches) = matches.subcommand_matches("test") {
        subcmd(matches, "test");
    } else if let Some(matches) = matches.subcommand_matches("run") {
        subcmd(matches, "run");
    } else if let Some(matches) = matches.subcommand_matches("module") {
        module_subcommand(matches)
    } else {
        panic!("unknown subcommand");
    }
}

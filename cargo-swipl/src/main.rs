use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use std::env;
use std::process::Command;
use swipl_info::*;

fn get_envs() -> Vec<(&'static str, String)> {
    let info = get_swipl_info();
    let mut result = Vec::new();

    if cfg!(target_os = "windows") {
        let path = env::var("PATH").unwrap_or_else(|_| "".to_owned());
        let path = format!("{};{}", info.lib_dir, path);
        result.push(("PATH", path));
    } else {
        let ld_library_path = env::var("LD_LIBRARY_PATH").unwrap_or_else(|_| "".to_owned());
        let ld_library_path = format!("{}:{}", info.lib_dir, ld_library_path);
        result.push(("LD_LIBRARY_PATH", ld_library_path));
    }

    result.push(("SWI_HOME_DIR", info.swi_home));

    result
}

fn set_library_path(command: &mut Command) {
    for (var, val) in get_envs() {
        command.env(var, val);
    }
}

fn subcmd(subcommand: &ArgMatches, cmd: &str) {
    let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
    let mut command = Command::new(cargo);

    set_library_path(&mut command);

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

fn print_info(lib_only: bool) {
    let info = get_swipl_info();

    if lib_only {
        println!("{}", info.lib_dir);
    } else {
        println!(
            "version: {}\nswihome: {}\nlibrary path: {}",
            info.version, info.swi_home, info.lib_dir
        );
    }
}

fn list_envs() {
    for (var, val) in get_envs() {
        println!("{var}={val}");
    }
}

fn arbitrary_command(subcommand: &ArgMatches) {
    if let Some(mut m) = subcommand.values_of("cmd") {
        let first = m.next();
        if first.is_none() {
            eprintln!("Error: no subcommand given");
            std::process::exit(1);
        }
        let command_name = first.unwrap();
        let mut command = Command::new(command_name);
        set_library_path(&mut command);
        let rest: Vec<_> = m.collect();
        command.args(rest);

        let exit_status = command
            .spawn()
            .unwrap_or_else(|e| {
                eprintln!("cargo-swipl: {}: {}", command_name, e);
                let code = e.raw_os_error();
                std::process::exit(code.unwrap_or(1));
            })
            .wait()
            .unwrap();

        if let Some(code) = exit_status.code() {
            std::process::exit(code);
        }
    } else {
        eprintln!("Error: no subcommand given");
        std::process::exit(1);
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
            SubCommand::with_name("info")
                .about("print information about the swipl environment")
                .arg(Arg::with_name("lib_only")
                    .help("only print library path (useful for debuggers)")
                    .short("l").required(false))
        )
        .subcommand(
            SubCommand::with_name("env")
                .setting(AppSettings::TrailingVarArg)
                .setting(AppSettings::AllowLeadingHyphen)
                .about("run an arbitrary command in an environment where the swipl library is added to the load path")
                .arg(Arg::from_usage("<cmd>... 'commands to run'").required(false))
        )
        .subcommand(
            SubCommand::with_name("listenv")
                .about("list the environment variables that would be applied if the env subcommand was used")
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
    } else if let Some(matches) = matches.subcommand_matches("info") {
        print_info(matches.is_present("lib_only"));
    } else if let Some(matches) = matches.subcommand_matches("env") {
        arbitrary_command(matches);
    } else if let Some(_matches) = matches.subcommand_matches("listenv") {
        list_envs();
    } else {
        panic!("unknown subcommand");
    }
}

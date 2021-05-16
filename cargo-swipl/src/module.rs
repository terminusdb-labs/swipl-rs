use swipl_macros_parse::predicate::*;
use clap::ArgMatches;
use syn::{self, Item, Visibility};
use std::io;
use std::path::{Path, PathBuf};
use tempfile::tempfile;

use std::env;
use std::process::Command;

pub fn module_subcommand(matches: &ArgMatches) {
    let cmd = cargo_metadata::MetadataCommand::new();
    let metadata = cmd.exec().unwrap();

    // take package specified with -p
    let mut package = None;
    if let Some(package_name) = matches.value_of("package") {
        for p in metadata.packages.iter() {
            if p.name == package_name {
                // is this a workspace member?
                if metadata.workspace_members.iter().any(|p_id| &p.id == p_id) {
                    package = Some(p);
                    break;
                } else {
                    panic!("not a workspace package");
                }
            }
        }
        if package.is_none() {
            panic!("package not found");
        }
    } else {
        if let Some(p) = metadata.root_package() {
            package = Some(p);
        } else {
            panic!("no package specified and no root package exists");
        }
    }

    let package = package.unwrap();
    println!("selected package {:?}", package.name);
    let module_name = str::replace(&package.name, "-", "_");

    println!("lets build");
    let cargo = env::var("CARGO").unwrap_or("cargo".to_owned());
    let mut command = Command::new(cargo);
    command.arg("build");

    let exit_status = command.spawn().unwrap().wait().unwrap();
    
    if let Some(code) = exit_status.code() {
        if code != 0 {
            std::process::exit(code);
        }
    }

    // ok build worked out great so now we can find the thing
    
    let rlib_name = format!("target/debug/lib{}.rlib", module_name);
    println!("rlib name: {}", rlib_name);
    let mut lib_path = package.manifest_path.clone();
    lib_path.pop();
    lib_path.push("src");
    lib_path.push("lib.rs");

    // find all the definitions hurray
    let definitions = find_definitions_in_file(lib_path.into());


    //let mut file = tempfile().unwrap();
    let mut file = std::fs::File::create("install.rs").unwrap();
    generate_install_rs(&mut file, &module_name, &definitions).unwrap();


}

fn find_definitions_in_file(path: PathBuf) -> Vec<(Vec<String>, String)> {
    let mut result = Vec::new();
    for_each_module(
        &path,
        |module_path, contents| {
            for item in contents {
                if let Item::Macro(item) = item {
                    if let Some(macro_name) = item.mac.path.segments.last() {
                        if macro_name.ident == "predicates" {
                            // we found a block! :D
                            if let Ok(definitions) = syn::parse2::<ForeignPredicateDefinitionBlock>(item.mac.tokens.clone()) {

                                for definition in definitions.definitions {
                                    result.push((module_path.iter().map(|s|s.to_string()).collect(), definition.predicate.rust_name().to_string()));
                                    println!("{:?} {}", module_path, definition.predicate.rust_name())
                                }
                            }
                        }
                    }
                }
            }
        }).unwrap();

    result
}

fn for_each_module(path: &PathBuf, mut f: impl FnMut(&[&str], &[Item])) -> io::Result<()> {
    let dir_path = path.parent().unwrap_or_else(||Path::new("./")).into();
    for_each_module_in_file(&path, &dir_path, &[], &mut f)
}

fn for_each_module_in_file(file_path: &PathBuf, dir_path: &PathBuf, module_path: &[&str], f: &mut impl FnMut(&[&str], &[Item])) -> io::Result<()> {
    let contents = std::fs::read_to_string(&file_path).unwrap();
    let file = syn::parse_file(&contents).unwrap();

    for_each_module_in_items(&dir_path, module_path, file.items.as_slice(), f)
}

fn for_each_module_in_items(dir_path: &PathBuf, module_path: &[&str], items: &[Item], f: &mut impl FnMut(&[&str], &[Item])) -> io::Result<()> {
    f(module_path, items);

    for item in items {
        if let Item::Mod(m) = item {
            // is it public?
            if let Visibility::Public(_) = m.vis {
                let name = &m.ident;
                let name_string = name.to_string();
                let mut new_module_path = module_path.to_vec();
                new_module_path.push(&name_string);
                let module_dir_path = dir_path.join(&name_string);
                // is it a module definition or a reference to another file?
                if let Some((_, content)) = &m.content {
                    for_each_module_in_items(&module_dir_path, &new_module_path, content.as_slice(), f)?;
                }
                else {
                    // module definition is in a file.
                    // this file is either <name>.rs or <name>/mod.rs.
                    // <name>.rs takes precedence if it exists.
                    let module_file_path = dir_path.join(format!("{}.rs", name));
                    if module_file_path.exists() {
                        for_each_module_in_file(&module_file_path, &module_dir_path, &new_module_path, f)?;
                    } else {
                        let module_file_path = module_dir_path.join("mod.rs");
                        if module_file_path.exists() {
                            for_each_module_in_file(&module_file_path, &module_dir_path, &new_module_path, f)?;
                        }
                        else {
                            return Err(io::Error::new(io::ErrorKind::NotFound, "module file not found"));
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

pub fn generate_install_rs<W: io::Write>(output: &mut W, package_name: &str, predicates: &[(Vec<String>, String)]) -> io::Result<()> {
    write!(output, r#"
use {};

#[no_mangle]
extern "C" fn install() {{
"#, package_name)?;

    for (path, predicate) in predicates {
        if path.is_empty() {
            writeln!(output, "    {}::register_{}();", package_name, predicate)?;
        } else {
            writeln!(output, "    {}::{}::register_{}();", package_name, path.join("::"), predicate)?;
        }
    }

    writeln!(output, "}}")?;

    output.flush()?;

    Ok(())
}

// rustc --edition 2018 --crate-type cdylib install.rs --extern terminus_store_prolog=target/debug/libterminus_store_prolog.rlib -L target/debug/deps -L /home/matthijs/.swivm/versions/v8.2.4/lib/swipl/lib/x86_64-linux

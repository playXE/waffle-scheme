use comet::{
    immix::{instantiate_immix, ImmixOptions},
    letroot,
};
use comet_extra::alloc::vector::Vector;
use rustyline::{config::Configurer, Editor};
use std::{mem::size_of, path::PathBuf};
use structopt::StructOpt;
use waffle::{
    bytecompiler::ByteCompiler,
    compiler::{Compiler, Op},
    jit::{bc2lbc::BC2LBC, c1::C1JIT},
    runtime::{
        add_module_search_path, load_file, make_symbol,
        value::{Null, Value},
        NanBoxedDecoder, Runtime, SchemeThread,
    },
};

#[derive(Debug, StructOpt)]
#[structopt(name = "waffle", about = "A simple Scheme bytecode VM")]
pub struct Options {
    #[structopt(long, help = "Prints debug messages during compilation process")]
    debug_cc: bool,
    #[structopt(long, help = "Prints Cranelift IR and assembly of JIT compiled code")]
    dump_jit: bool,
    #[structopt(
        long,
        help = "Threshold after which we compile Scheme code using JIT",
        default_value = "10"
    )]
    hotness: usize,
    #[structopt(
        long,
        help = "Changes GC verbose level: 1 - least verbose, 2 - most verbose",
        default_value = "0"
    )]
    gc_verbose: u8,
    #[structopt(long, help = "Sets GC heap size (in MB)", default_value = "128")]
    heap_size: usize,
    #[structopt(
        long,
        help = "Sets heap size threashol before starting GC cycle",
        default_value = "64"
    )]
    heap_initial_size: usize,
    #[structopt(long, help = "Sets minimal heap size threshold", default_value = "4")]
    heap_min_size: usize,
    #[structopt(long, help = "Sets maximal heap size threshold", default_value = "128")]
    heap_max_size: usize,
    #[structopt(short = "I", help = "Module search paths")]
    module_search_paths: Vec<String>,
    #[structopt(parse(from_os_str))]
    filename: Option<PathBuf>,
}

fn main() {
    let opts = Options::from_args();

    let immix_opts = ImmixOptions::default()
        .with_verbose(opts.gc_verbose)
        .with_heap_size(opts.heap_size * 1024 * 1024)
        .with_max_heap_size(opts.heap_max_size * 1024 * 1024)
        .with_min_heap_size(opts.heap_min_size * 1024 * 1024)
        .with_initial_size(opts.heap_initial_size * 1024 * 1024);
    let immix = instantiate_immix::<NanBoxedDecoder>(immix_opts);
    let mut thread = Runtime::new(immix, opts.debug_cc, opts.dump_jit, opts.hotness);
    add_module_search_path(&mut thread, "./");
    for path in opts.module_search_paths.iter() {
        add_module_search_path(&mut thread, path);
    }

    let mut cc = ByteCompiler::new(&mut *thread, None, None, 0);

    let l = cc.new_local();

    cc.while_loop::<(), _, _>(
        &mut *thread,
        |_thread, cc| {
            cc.get_local(l);
            Ok(())
        },
        |thread, cc| {
            cc.int32(42);
            let name = make_symbol(thread, "displayln");
            assert!(cc.variabe_ref(thread, name));
            cc.apply(1);
            //cc.pop_();
            Ok(())
        },
    )
    .unwrap();
    let proto = cc.end(&mut *thread, 1, false);

    let mut jit = C1JIT::new();

    jit.compile(&mut *thread, proto, true);

    /* let mut cc = Compiler::new(&mut thread, None, None, 0);
    let reader = std::fs::File::open(opts.filename.unwrap()).unwrap();
    let mut reader = lexpr::Parser::from_reader(reader);
    let mut exprs = Vector::new(&mut thread.mutator);
    let mut macros = Vector::new(&mut thread.mutator);
    for expr in reader.datum_iter() {
        match expr {
            Ok(datum) => {
                let val = datum.value();

                match cc.parse(&mut thread, val, &mut macros) {
                    Ok(val) => {
                        if !val.is_undefined() {
                            exprs.push(&mut thread.mutator, val);
                        }
                    }
                    Err(e) => {
                        eprintln!(
                            "failed to parse at {}:{}: {}",
                            datum.span().start().line(),
                            datum.span().start().column(),
                            e
                        );
                        return;
                    }
                }
            }
            Err(e) => {
                eprintln!("{}", e);
                return;
            }
        }
    }

    for expr in exprs.iter() {
        println!("parsed: {}", expr);
    }

    /*
    /*let mut cc = Compiler::new(&mut thread, None, None, 0);
    let sexp = lexpr::from_str("1").unwrap();
    let _ = cc.compile(&mut thread, &sexp, false);
    let proto = cc.end(&mut thread, 0, false);
    let mut jit = MethodJIT::new();
    let code = jit.compile(proto);*/

    if let Some(ref file) = opts.filename {
        match load_file(&mut thread, file, Value::new(Null)) {
            Ok(x) => {
                println!("Success: {}", x)
            }
            Err(e) => {
                println!("Error: {}", e);
            }
        }
        let rt = thread.runtime;
        Runtime::terminate(rt, &thread.mutator);
    } else {
        repl(&mut thread);
    }*/*/
}

fn repl(thread: &mut SchemeThread) {
    let mut config = rustyline::Config::builder();
    config.set_completion_type(rustyline::CompletionType::Circular);
    config.set_bell_style(rustyline::config::BellStyle::Visible);
    config.set_edit_mode(rustyline::EditMode::Emacs);
    config.set_color_mode(rustyline::ColorMode::Enabled);
    let mut rl = Editor::<()>::with_config(config.build());
    let stack = thread.mutator.shadow_stack();
    let cc = Compiler::new(thread, None, None, 0);
    letroot!(cc = stack, cc);
    loop {
        let readline = rl.readline("waffle>");
        match readline {
            Ok(line) => {
                let expr = match lexpr::from_str(&line) {
                    Ok(expr) => expr,
                    Err(e) => {
                        eprintln!("Failed to read '{}': {}", line, e);
                        continue;
                    }
                };

                match cc.compile(thread, &expr, false) {
                    Ok(_) => (),
                    Err(e) => {
                        cc.clear();
                        eprintln!("{}", e);
                        continue;
                    }
                }
                let p = cc.end(thread, 0, false);
                cc.clear();
                match waffle::runtime::vm::apply(thread, Value::new(p), &[]) {
                    Ok(x) => {
                        println!("{}", x);
                    }
                    Err(e) => {
                        eprintln!("runtime error: {}", e);
                        continue;
                    }
                }
            }
            Err(rustyline::error::ReadlineError::Eof) => {
                break;
            }

            Err(err) => {
                eprintln!("{}", err);
            }
        }
    }
}

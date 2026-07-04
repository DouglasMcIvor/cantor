use std::io::Write as _;
use std::path::PathBuf;
use std::process::{Command, Stdio};

pub fn cantor() -> Command {
    Command::new(env!("CARGO_BIN_EXE_cantor"))
}

pub fn fixture(name: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("tests/cantor_files");
    p.push(name);
    p
}

#[derive(Debug)]
pub struct Output {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
}

pub fn run(args: &[&str]) -> Output {
    let mut cmd = cantor();
    for &a in args {
        cmd.arg(a);
    }
    let out = cmd.output().expect("failed to spawn cantor binary");
    Output {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code().unwrap_or(-1),
    }
}

pub fn run_repl(input: &str) -> Output {
    let mut cmd = cantor();
    cmd.stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("failed to spawn cantor binary");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");
    drop(child.stdin.take());
    let out = child
        .wait_with_output()
        .expect("failed to wait for cantor binary");
    Output {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code().unwrap_or(-1),
    }
}

pub fn run_file(name: &str) -> Output {
    let path = fixture(name);
    run(&[path.to_str().unwrap()])
}

pub fn run_subcommand(name: &str) -> Output {
    let path = fixture(name);
    run(&["run", path.to_str().unwrap()])
}

pub fn run_llvm_ir(name: &str) -> Output {
    let path = fixture(name);
    run(&["llvm-ir", path.to_str().unwrap()])
}

/// Assert that `cantor run` refused to execute (the `ConstrainedTree` proof
/// gate — not every signature was `Proved`), regardless of whether the
/// culprit is a `Counterexample` or an `Unknown`.
pub fn assert_run_refused(out: &Output) {
    assert_ne!(
        out.code, 0,
        "should refuse to run\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not running"),
        "expected refusal message on stderr:\n{}",
        out.stderr
    );
}

/// Assert that `cantor run` refused to execute because at least one signature
/// was `Unknown` — the `ConstrainedTree` proof gate means this is no longer
/// the "warning: ... running anyway" case it used to be.
pub fn assert_run_refused_due_to_unknown(out: &Output) {
    assert_run_refused(out);
    assert!(
        out.stdout.contains("  unknown  "),
        "expected an `unknown` line in the check report:\n{}",
        out.stdout
    );
}

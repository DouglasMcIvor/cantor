use std::io::{Read as _, Write as _};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

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

/// Like `run_subcommand`, but pipes `input` to the child's `stdin` instead
/// of leaving it closed (`run`'s plain `.output()` closes stdin immediately,
/// which is itself a valid — if trivial — "EOF right away" test case for an
/// event-loop program). Mirrors `run_repl`'s piping, with `run <fixture>`
/// args instead of the bare REPL invocation.
pub fn run_subcommand_with_stdin(name: &str, input: &str) -> Output {
    let path = fixture(name);
    let mut cmd = cantor();
    cmd.arg("run")
        .arg(&path)
        .stdin(Stdio::piped())
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

pub fn run_llvm_ir(name: &str) -> Output {
    let path = fixture(name);
    run(&["llvm-ir", path.to_str().unwrap()])
}

/// Like `run_subcommand`, but kills the child and returns `None` instead of
/// blocking forever if it doesn't exit within `timeout` — cvc5 is known not
/// to honor the CLI's own `--timeout` (`tlimit`) for some nonlinear-arithmetic
/// query shapes (see `known_issues.rs`'s module doc), so a genuinely-hanging
/// fixture would otherwise wedge the whole test binary. Reads stdout/stderr
/// on background threads while polling so a full pipe buffer can't deadlock
/// the wait.
pub fn run_subcommand_with_deadline(name: &str, timeout: Duration) -> Option<Output> {
    let path = fixture(name);
    let mut child = cantor()
        .arg("run")
        .arg(&path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn cantor binary");

    let mut stdout_pipe = child.stdout.take().expect("child stdout not piped");
    let mut stderr_pipe = child.stderr.take().expect("child stderr not piped");
    let stdout_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout_pipe.read_to_end(&mut buf);
        buf
    });
    let stderr_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr_pipe.read_to_end(&mut buf);
        buf
    });

    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("failed to poll child") {
            break Some(status);
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };

    let stdout_buf = stdout_thread.join().expect("stdout reader thread panicked");
    let stderr_buf = stderr_thread.join().expect("stderr reader thread panicked");
    let status = status?;
    Some(Output {
        stdout: String::from_utf8_lossy(&stdout_buf).into_owned(),
        stderr: String::from_utf8_lossy(&stderr_buf).into_owned(),
        code: status.code().unwrap_or(-1),
    })
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

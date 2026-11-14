use anyhow::Result;
use obb_broker::{RemoteCmdOutput, RemoteExecutor};
use std::collections::HashMap;
use std::sync::Mutex;

/// Deterministic offline mock SSH executor for fast unit & integration tests.
#[derive(Default)]
pub struct MockSshExecutor {
    responses: HashMap<String, RemoteCmdOutput>,
    pub calls: Mutex<Vec<(String, String)>>,
}

impl MockSshExecutor {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_host_output(mut self, host: &str, output: RemoteCmdOutput) -> Self {
        self.responses.insert(host.to_string(), output);
        self
    }

    pub fn recorded_calls(&self) -> Vec<(String, String)> {
        self.calls.lock().unwrap().clone()
    }
}

impl RemoteExecutor for MockSshExecutor {
    fn run_ssh(
        &self,
        host: &str,
        remote_script: &str,
        _timeout_secs: u64,
    ) -> Result<RemoteCmdOutput> {
        self.calls
            .lock()
            .unwrap()
            .push((host.to_string(), remote_script.to_string()));
        if let Some(resp) = self.responses.get(host) {
            Ok(resp.clone())
        } else {
            Ok(RemoteCmdOutput {
                exit_code: 255,
                stdout: String::new(),
                stderr: format!("mock: host `{host}` unreachable"),
                duration_ms: 1,
            })
        }
    }
}

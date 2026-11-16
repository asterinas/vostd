use crate::config::Config;
#[allow(unused_imports)]
pub use colored::Colorize;
use log;
use log::Record;
use log4rs::{
    self,
    append::{
        console::ConsoleAppender,
        rolling_file::{
            policy::compound::{
                roll::fixed_window::FixedWindowRoller, trigger::size::SizeTrigger, CompoundPolicy,
            },
            RollingFileAppender,
        },
    },
    config::Appender,
    encode::{
        json::JsonEncoder, pattern::PatternEncoder, writer::simple::SimpleWriter, Encode, Write,
    },
};
use std::sync::Once;

pub struct Console {}
static CONSOLE_INIT: Once = Once::new();

#[derive(Debug, Clone)]
pub struct TruncateEncoder {
    pub inner: PatternEncoder,
    pub max_len: usize,
}

impl TruncateEncoder {
    pub fn new(max_len: usize) -> Self {
        TruncateEncoder {
            inner: PatternEncoder::new("{m}{n}"),
            max_len,
        }
    }
}

impl Encode for TruncateEncoder {
    fn encode(&self, w: &mut dyn Write, record: &Record) -> anyhow::Result<()> {
        let mut buf = SimpleWriter(Vec::<u8>::new());
        self.inner.encode(&mut buf, record)?;

        let s = String::from_utf8_lossy(&buf.0);
        let truncated = if s.len() > self.max_len {
            let mut end = self.max_len;
            while !s.is_char_boundary(end) {
                end -= 1;
            }
            let mut truncated = String::from(&s[..end]);
            truncated.push_str("...\n");
            truncated
        } else {
            s.to_string()
        };
        let colored = match record.level() {
            log::Level::Error => truncated.red(),
            log::Level::Warn => truncated.yellow(),
            log::Level::Info => truncated.blue(),
            log::Level::Debug => truncated.bright_black(),
            _ => truncated.normal(),
        };

        w.write_all(colored.to_string().as_bytes())?;
        Ok(())
    }
}

fn init_console() {
    CONSOLE_INIT.call_once(|| {
        let max_width = Config::new().get("LOG_MAX_CONSOLE_WIDTH").unwrap_or(320);
        let console = ConsoleAppender::builder()
            .encoder(Box::new(TruncateEncoder::new(max_width)))
            .build();

        let roller = FixedWindowRoller::builder()
            .base(1)
            .build("xtask.log.{}.json.gz", 3)
            .unwrap();
        let trigger = SizeTrigger::new(10 * 1024 * 1024); // 10MB
        let policy = CompoundPolicy::new(Box::new(trigger), Box::new(roller));
        let json = RollingFileAppender::builder()
            .encoder(Box::new(JsonEncoder::new()))
            .build("xtask.log.json", Box::new(policy))
            .unwrap();

        let config = log4rs::Config::builder()
            .appender(Appender::builder().build("console", Box::new(console)))
            .appender(Appender::builder().build("json", Box::new(json)))
            .build(
                log4rs::config::Root::builder()
                    .appender("console")
                    .appender("json")
                    .build(log::LevelFilter::Debug),
            )
            .unwrap();
        log4rs::init_config(config).unwrap();
    });
}

impl Default for Console {
    fn default() -> Self {
        init_console();
        Console {}
    }
}

impl Console {
    pub fn new() -> Self {
        Console::default()
    }

    pub fn info(&self, msg: &str) {
        log::info!("{}", msg);
    }

    pub fn error(&self, msg: &str) -> ! {
        log::error!("{}", msg);
        std::process::exit(1);
    }

    pub fn warn(&self, msg: &str) {
        log::warn!("{}", msg);
    }

    pub fn debug(&self, msg: &str) {
        log::debug!("{}", msg);
    }

    pub fn status(&self, msg: &str) {
        log::info!("{}", msg);
    }

    pub fn fatal(&self, msg: &str) -> ! {
        let bt = std::backtrace::Backtrace::capture();
        log::error!("{}\nBacktrace:\n{}", msg, bt);
        std::process::exit(1);
    }
}

#[macro_export]
macro_rules! fatal {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .fatal(&format!($($arg)*))
        }
    }

#[macro_export]
macro_rules! error {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .error(&format!($($arg)*));
        }
    }

#[macro_export]
macro_rules! info {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .info(&format!($($arg)*));
        }
    }

#[macro_export]
macro_rules! debug {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .debug(&format!($($arg)*));
        }
    }

#[macro_export]
macro_rules! status {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .status(&format!($($arg)*));
        }
    }

#[macro_export]
macro_rules! warn {
        ($($arg:tt)*) => {
            $crate::console::Console::new()
                .warn(&format!($($arg)*));
        }
    }

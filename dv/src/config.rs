use dotenv::dotenv;
use std::sync::Once;

pub struct Config {}

static CONFIG_LOADED: Once = Once::new();

fn load_config() {
    CONFIG_LOADED.call_once(|| {
        dotenv().ok();
    });
}

impl Default for Config {
    fn default() -> Self {
        load_config();
        Config {}
    }
}

impl Config {
    pub fn new() -> Self {
        Config::default()
    }

    pub fn get<T>(&self, key: &str) -> Option<T>
    where
        T: std::str::FromStr,
        T::Err: std::fmt::Debug,
    {
        std::env::var(key).ok().and_then(|v| v.parse::<T>().ok())
    }
}

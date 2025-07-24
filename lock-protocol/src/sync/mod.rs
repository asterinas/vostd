pub mod rcu;
pub(crate) mod spin;

/// Registers a callback to be invoked after the current grace period.
pub(crate) fn after_grace_period<F: FnOnce() + Send + 'static>(callback: F) {
    // let rcu_monitor = RCU_MONITOR.get().unwrap();
    // rcu_monitor.after_grace_period(callback);
}

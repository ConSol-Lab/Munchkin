pub(crate) mod checking;
pub(crate) mod processing;

mod logging;
pub(crate) use logging::*;

/// The string labels for the different inference rules implemented by the various propagators.
pub(crate) mod inference_labels {
    pub(crate) const LINEAR: &str = "linear";
    pub(crate) const ELEMENT: &str = "element";
    pub(crate) const MAXIMUM: &str = "maximum";
    pub(crate) const ALL_DIFFERENT: &str = "all_different";
    pub(crate) const TIME_TABLE: &str = "time_table";
    pub(crate) const PREVENT_AND_CHECK: &str = "prevent_and_check";
}

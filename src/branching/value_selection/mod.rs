//! Provides the [`ValueSelector`] trait which is required
//! for value selectors to implement; the main method in this trait relies on
//! [`ValueSelector::select_value`].
//!
//! Furthermore, it defines several implementations of the [`ValueSelector`] trait such as
//! [`InDomainMin`], [`PhaseSaving`] and [`SolutionGuidedValueSelector`]. Any [`ValueSelector`]
//! should only select values which are in the domain of the provided variable.

mod in_domain_min;
mod value_selector;

pub use in_domain_min::*;
pub use value_selector::ValueSelector;

use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;

mod processor;
mod rp_engine;

use anyhow::Context;
use drcp_format::reader::ProofReader;
use drcp_format::steps::Conclusion;
use drcp_format::writer::ProofWriter;
use drcp_format::Format;
pub(crate) use processor::Processor;

use crate::proof::ProofLiterals;
use crate::variables::Literal;

/// Processes a proof. This means the nogoods are trimmed, and the inferences are introduced to
/// make a complete proof.
pub(crate) fn process_proof<R: Read>(
    mut processor: Processor,
    reader: ProofReader<R, ProofLiterals>,
    output: PathBuf,
) -> anyhow::Result<()> {
    // To process the proof, we do the following:
    // 1. Trim the redundant nogoods.
    // 2. Introduce the inferences for the remaining nogoods.
    // 3. Finalize the proof with the correct conclusion.

    // 1. Trim the nogoods.
    let (nogoods, conclusion) = trim(&mut processor, reader)?;

    println!("%% nogoodsAfterTrimming={}", nogoods.len());

    // 2. Introduce inferences.
    let file = File::create(&output)
        .with_context(|| format!("Failed to create proof file {}.", output.display()))?;
    let mut writer = ProofWriter::new(Format::Text, file, ProofLiterals::default());
    introduce_inferences(&mut processor, nogoods, &mut writer)?;

    println!(
        "%% numberOfInferences={}",
        writer.get_number_of_inferences()
    );

    // 3. Finalize the proof
    let literals = match conclusion {
        Conclusion::Unsatisfiable => writer.unsat()?,
        Conclusion::Optimal(bound) => writer.optimal(bound)?,
    };
    let literals_file_path = output.with_extension("lits");
    let literals_file = File::create(&literals_file_path)
        .with_context(|| format!("Failed to create file {}", literals_file_path.display()))?;
    processor.write_proof_literals(literals, literals_file)?;

    Ok(())
}

/// Reads the nogoods from the scaffold, and returns a list of nogoods that does not contain
/// redundant nogoods. Also returns the conclusion of the proof.
#[allow(unused_variables, reason = "will be used in assignment")]
pub(crate) fn trim<R: Read>(
    processor: &mut Processor,
    scaffold: ProofReader<R, ProofLiterals>,
) -> anyhow::Result<(Vec<Vec<Literal>>, Conclusion<Literal>)> {
    // A nogood is a vector of literals. The order of the literals in the nogood does not matter.
    //
    // The order of the list *must* be the same as the order in the scaffold. The output of this
    // function should not re-order nogoods. Ensure you only remove nogoods from the scaffold.
    //
    // You should use the processor to do the trimming. In particular, use:
    // - `Processor::add_removable_nogood()` to add nogoods to the processor. This may return a
    //   conflict (more on that later).
    // - `Processor::remove_nogood()` to remove the last added nogood.
    // - `Processor::propagate_under_assumptions()` to run the propagation. It will either return a
    //   conflict or not.
    //
    // More on conflicts:
    // A conflict is a collection of edges in the implication graph. We discriminate between edges
    // that are from nogoods added with `Processor::add_removable_nogood()` and propagations
    // performed by propagators. For trimming you are not concerned with the propagations by
    // propagators, but you want to know which other nogoods are used to derive the conflict.

    todo!()
}

/// Writes a proof to the given writer, adding the appropriate inferences. The nogoods are given in
/// the order of the proof; there is no need to reverse anything here.
#[allow(unused_variables, reason = "will be used in assignment")]
pub(crate) fn introduce_inferences<W: Write>(
    processor: &mut Processor,
    nogoods: Vec<Vec<Literal>>,
    writer: &mut ProofWriter<W, ProofLiterals>,
) -> anyhow::Result<()> {
    // Performing inference introduction is very similar to trimming, except you can go through the
    // list of nogoods in the forward direction. Use the same functions on the processor as in the
    // trimming phase.
    //
    // When a conflict is encountered, you have to log
    // the propagation edges with `ProofWriter::log_inference` and the nogood edges with
    // `ProofWriter::log_nogood`. Ensure that you keep track of the step IDS to appropriately
    // supply the hints to the proof writer.

    todo!("implement introduction of inferences");
}

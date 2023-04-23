use bellperson::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub trait ExposedConstraintSystem<Scalar: PrimeField>: Sized + Send
where
  Self: ConstraintSystem<Scalar>,
{
  fn expose_aux<AR, A>(
    &mut self,
    aux_set_number: usize,
    aux_item_annotation: A,
  ) -> Result<(), SynthesisError>
  where
    A: FnOnce() -> AR,
    AR: Into<String>;
}

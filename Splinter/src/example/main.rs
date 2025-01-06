pub mod BankSpec_t;
pub mod BankContract_t;
pub mod Bank_v;
pub mod ClientAPI_t;
pub mod VerifiedEntry_t;

pub mod BankObligations_v;
pub mod SimpleBank_v;

fn main() {
    VerifiedEntry_t::entry::<SimpleBank_v::SimpleBank>();
}
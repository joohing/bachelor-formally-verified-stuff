fn main() {
    let _ = add_vec(
        vec![Jonaint::from(1),
             Jonaint::from(2),
             Jonaint::from(3)
            ],
        vec![Jonaint::from(4),
             Jonaint::from(5),
             Jonaint::from(6)
            ]
    );
}

#[derive(Copy, Clone)]
#[hax_lib::attributes]
struct Jonaint {
    #[hax_lib::refine(v < Jonaint::MAX)]
    v: u8,
}

impl Jonaint { const MAX: u8 = 10; }

impl std::ops::Add for Jonaint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self { v: (self.v + rhs.v) % Jonaint::MAX }
    }
}

impl From<u8> for Jonaint {
    fn from(n: u8) -> Self {
        Self { v: n % Jonaint::MAX }
    }
}

#[hax_lib::requires(l.len() == r.len())]
#[hax_lib::fstar::options("--z3rlimit 100")]
fn add_vec(l: Vec<Jonaint>, r: Vec<Jonaint>) -> Vec<Jonaint> {
    let mut result = Vec::with_capacity(l.len());

    // Loop through the indices of the vectors
    for i in 0..l.len() {
        hax_lib::loop_decreases!(l.len() - i);

        let sum = l[i] + r[i];
        result.push(sum);
    }

    result
}

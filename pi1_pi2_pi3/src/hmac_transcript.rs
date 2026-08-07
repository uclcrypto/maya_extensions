use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(data);
    mac.finalize().into_bytes().into()
}


pub struct HmacTranscript {
    state: [u8; 32],
}

impl HmacTranscript {
    //Init(label)
    pub fn new(label: &[u8]) -> Self {
        let state = hmac_sha256(&[0u8; 32], label);
        Self { state }
    }

    //Append(label, data)
    pub fn append_message(&mut self, label: &[u8], data: &[u8]) {
        use hmac::{Hmac, Mac};
        use sha2::Sha256;
        type HmacSha256 = Hmac<Sha256>;

        let mut mac = HmacSha256::new_from_slice(&self.state)
            .expect("HMAC accepts any key length");
        mac.update(label);
        mac.update(&[0x00]);
        mac.update(&(data.len() as u32).to_le_bytes());
        mac.update(data);
        self.state = mac.finalize().into_bytes().into();
    }

    pub fn challenge_bytes(&mut self, label: &[u8], dest: &mut [u8]) {
        use hmac::{Hmac, Mac};
        use sha2::Sha256;
        type HmacSha256 = Hmac<Sha256>;

        assert!(dest.len() <= 64, "challenge_bytes: dest must be at most 64");

        // h1 = H(state, "chal" || 0x00 || label)
        let h1: [u8; 32] = {
            let mut mac = HmacSha256::new_from_slice(&self.state)
                .expect("HMAC key");
            mac.update(b"chal");
            mac.update(&[0x00]);
            mac.update(label);
            mac.finalize().into_bytes().into()
        };

        if dest.len() <= 32 {
            dest.copy_from_slice(&h1[..dest.len()]);
        } else {
            // h2 = H(state, "chal_ext" || 0x00 || h1)
            let h2: [u8; 32] = {
                let mut mac = HmacSha256::new_from_slice(&self.state)
                    .expect("HMAC key");
                mac.update(b"chal_ext");
                mac.update(&[0x00]);
                mac.update(&h1);
                mac.finalize().into_bytes().into()
            };
            // dest = h1 || h2
            dest[..32].copy_from_slice(&h1);
            dest[32..64].copy_from_slice(&h2);
        }

        // state = H(state, "chal_update" || 0x00 || h1)
        let mut mac = HmacSha256::new_from_slice(&self.state)
            .expect("HMAC key");
        mac.update(b"chal_update");
        mac.update(&[0x00]);
        mac.update(&h1);
        self.state = mac.finalize().into_bytes().into();
    }

    pub fn witness_rng_seed(&self, witness: &[u8]) -> [u8; 32] {
        use hmac::{Hmac, Mac};
        use sha2::Sha256;
        type HmacSha256 = Hmac<Sha256>;

        let mut mac = HmacSha256::new_from_slice(&self.state)
            .expect("HMAC key");
        mac.update(b"witness_rng");
        mac.update(&[0x00]);
        mac.update(witness);
        mac.finalize().into_bytes().into()
    }
}

pub type Transcript = HmacTranscript;


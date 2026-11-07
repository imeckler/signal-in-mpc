//! Synthetic translator regressions only. Actual Prost sources are untouched.

pub fn branch_loop(enabled: bool, stop: u32) -> Result<u32, u8> {
    let mut index = 0;
    let value = match enabled {
        true => loop {
            if index == stop {
                break index;
            }
            if index == 3 {
                return Err(7);
            }
            index += 1;
        },
        false => 41,
    };
    Ok(value + 1)
}

pub fn branch_loop_mut(enabled: bool, stop: u32, state: &mut u32) -> Result<u32, u8> {
    let mut index = 0;
    let value = match enabled {
        true => loop {
            *state += 1;
            if index == stop {
                break index;
            }
            if index == 3 {
                return Err(7);
            }
            index += 1;
        },
        false => 41,
    };
    *state += 10;
    Ok(value + 1)
}

pub fn tail_loop(stop: u32) -> Result<u32, u8> {
    let mut index = 0;
    loop {
        if index == stop {
            return Ok(index);
        }
        if index == 3 {
            return Err(7);
        }
        index += 1;
    }
}

// Positive cases matching the actual Prost shape: the common continuation
// contains only assignments/aggregates and return, so the existing inliner
// already knows how to move it into the match branches.
pub fn branch_loop_return(enabled: bool, stop: u32) -> Result<u32, u8> {
    let mut index = 0;
    let value = match enabled {
        true => loop {
            if index == stop { break index; }
            if index == 3 { return Err(7); }
            index += 1;
        },
        false => 41,
    };
    Ok(value)
}

pub fn branch_loop_mut_return(enabled: bool, stop: u32, state: &mut u32) -> Result<u32, u8> {
    let mut index = 0;
    let value = match enabled {
        true => loop {
            *state += 1;
            if index == stop { break index; }
            if index == 3 { return Err(7); }
            index += 1;
        },
        false => 41,
    };
    *state = 10;
    Ok(value)
}

use prost::encoding::{DecodeContext, WireType};
fn prefix(mut n:u64)->Vec<u8> { let mut v=Vec::new();while n>=128{v.push((n as u8)|128);n>>=7;}v.push(n as u8);v }
fn main() {
    let mut cases=Vec::new();
    for size in 0..65 {
        for payload in [vec![b'a';size],vec![0xc2,0xa2].repeat(size/2),vec![0xff;size],vec![0xf0,0x90,0x80,0x80].repeat(size/4)] {
            for extra in [0,3] { let mut input=prefix(payload.len() as u64+extra);input.extend(&payload);input.extend([0x31,0x32]);cases.push(input); }
        }
    }
    cases.extend([vec![],vec![0x80],vec![0x80;10],vec![0xff;10],vec![0x80;9].into_iter().chain([2]).collect(),vec![0xc0,0],vec![1,0xed],vec![3,0xed,0xa0,0x80]]);
    let mut compared=0;
    for input in &cases {
        for wire in [WireType::Varint,WireType::SixtyFourBit,WireType::LengthDelimited,WireType::StartGroup,WireType::EndGroup,WireType::ThirtyTwoBit] {
            for old in [Vec::new(),vec!["old".to_owned()],vec!["first".to_owned(),"second".to_owned()]] {
                let mut actual=old.clone();let mut actual_input=&input[..];
                let actual_result=prost::encoding::string::merge_repeated(wire,&mut actual,&mut actual_input,DecodeContext::default());
                let mut expected=old;let mut expected_input=&input[..];let mut value=String::new();
                let expected_result=prost::encoding::string::merge(wire,&mut value,&mut expected_input,DecodeContext::default());
                if expected_result.is_ok(){expected.push(value);}
                assert_eq!(format!("{actual_result:?}"),format!("{expected_result:?}"));
                assert_eq!(actual,expected);assert_eq!(actual_input,expected_input);compared+=1;
            }
        }
    }
    println!("Compared {compared} native repeated-String errors, values and exact suffixes");
}

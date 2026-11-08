fn main() {
    let frames: &[(&'static str,&'static str)] = &[
        ("WebSocketMessage","r#type"),
        ("WebSocketMessage","request"),
        ("WebSocketMessage","response"),
        ("WebSocketResponseMessage","id"),
        ("WebSocketResponseMessage","status"),
        ("WebSocketResponseMessage","message"),
        ("WebSocketResponseMessage","body"),
        ("WebSocketResponseMessage","headers"),
        ("WebSocketRequestMessage","verb"),
        ("WebSocketRequestMessage","path"),
        ("WebSocketRequestMessage","body"),
        ("WebSocketRequestMessage","id"),
        ("WebSocketRequestMessage","headers"),
];
    let helpers: &[fn(&mut prost::DecodeError)] = &[
        prost::DecodeError::reference_push_literal_0,
        prost::DecodeError::reference_push_literal_1,
        prost::DecodeError::reference_push_literal_2,
        prost::DecodeError::reference_push_literal_3,
        prost::DecodeError::reference_push_literal_4,
        prost::DecodeError::reference_push_literal_5,
        prost::DecodeError::reference_push_literal_6,
        prost::DecodeError::reference_push_literal_7,
        prost::DecodeError::reference_push_literal_8,
        prost::DecodeError::reference_push_literal_9,
        prost::DecodeError::reference_push_literal_10,
        prost::DecodeError::reference_push_literal_11,
        prost::DecodeError::reference_push_literal_12,
];
    let mut checked=0;
    for seed in 0..128 {
        let mut original=prost::DecodeError::new(format!("seed{seed}"));
        for _ in 0..seed%5 { original.push("Existing", "prefix"); }
        for (i,(message,field)) in frames.iter().enumerate() {
            let mut expected=original.clone();let mut actual=original.clone();
            expected.push(message,field);helpers[i](&mut actual);
            assert_eq!(format!("{expected:?}"),format!("{actual:?}"));checked+=1;
        }
    }
    for seed in 0..16 {
        for (i,(m1,f1)) in frames.iter().enumerate() {
            for (j,(m2,f2)) in frames.iter().enumerate() {
                let mut expected=prost::DecodeError::new(format!("seed{seed}"));
                let mut actual=expected.clone();
                expected.push(m1,f1);expected.push(m2,f2);
                helpers[i](&mut actual);helpers[j](&mut actual);
                assert_eq!(format!("{expected:?}"),format!("{actual:?}"));checked+=1;
            }
        }
    }
    println!("Compared {checked} exact native error/stack/order outcomes");
}

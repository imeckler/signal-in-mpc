#![allow(dead_code, unexpected_cfgs)]
use std::io::{self,BufRead};
use serde_json::{Value,json};
pub type Block = cipher::array::Array<u8,cipher::consts::U16>;
mod fixslice;
fn words(v:&Value,key:&str)->Vec<u64>{v[key].as_array().unwrap().iter().map(|x|x.as_u64().unwrap()).collect()}
fn run(v:&Value)->Value {
 match v["mode"].as_str().unwrap(){
  "profile"=>json!({"debug_assertions":cfg!(debug_assertions),"pointer_bits":usize::BITS,"type":std::any::type_name::<std::iter::Zip<std::slice::IterMut<'static,u64>,std::slice::Iter<'static,u64>>>()}),
  "zip"=>{
   let mut state=words(v,"state");let keys=words(v,"keys");let a=v["left_start"].as_u64().unwrap()as usize;let b=v["right_start"].as_u64().unwrap()as usize;assert!(a<=state.len()&&b<=keys.len());
   let steps=v["steps"].as_u64().unwrap()as usize;let mut yielded=Vec::new();let mut hints=Vec::new();
   let mut left=state.iter_mut();for _ in 0..a{left.next();}
   let mut right=keys.iter();for _ in 0..b{right.next();}
   let mut zip=left.zip(right);
   for _ in 0..steps {
    let item=match zip.next(){Some((x,y))=>{let before=*x;*x^=*y;Some([before,*y])},None=>None};
    yielded.push(item);hints.push(zip.size_hint().0);
   }
   drop(zip);json!({"state":state,"keys":keys,"yielded":yielded,"remaining":hints})
  },
  "add"=>{
   let original=words(v,"state");let mut state:[u64;8]=original.clone().try_into().unwrap();let keys=words(v,"keys");
   let accepted=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||fixslice::fixture_add_key(&mut state,&keys))).is_ok();
   json!({"accepted":accepted,"state":state,"preserved":state.as_slice()==original.as_slice()})
  },
  "inverse"=>{
   let input=words(v,"state");match std::panic::catch_unwind(||fixslice::fixture_inverse(&input)){
    Ok(output)=>json!({"accepted":true,"blocks":output}),Err(_)=>json!({"accepted":false})}
  },
  _=>panic!("public fixture mode")
 }
}
fn main(){std::panic::set_hook(Box::new(|_|{}));for line in io::stdin().lock().lines(){let v:Value=serde_json::from_str(&line.unwrap()).unwrap();println!("{}",run(&v));}}

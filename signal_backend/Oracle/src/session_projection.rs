//! PUBLIC-fixture canonical-record update candidate. No host secret runtime API.
use crate::{storage,pqr};
use prost::Message;
fn u32be(b:&[u8])->u32{u32::from_be_bytes(b.try_into().unwrap())}
// 525-byte model state = sender136 || five receive69 || receivePQ44.
// Preserve ALL other canonical fields; reject profiles needing skipped-key or
// PQ epoch/phase changes rather than silently discarding their retained state.
pub fn apply_receive(record:&storage::RecordStructure,state:&[u8])->Result<storage::RecordStructure,&'static str>{
 if state.len()!=525{return Err("selected state width")}
 let mut out=record.clone();let s=out.current_session.as_mut().ok_or("no current session")?;
 let sender=s.sender_chain.as_mut().ok_or("no sender")?;
 if !sender.message_keys.is_empty(){return Err("sender skipped keys unsupported")}
 s.root_key=state[0..32].to_vec();sender.sender_ratchet_key_private=state[32..64].to_vec();sender.sender_ratchet_key=[&[5u8][..],&state[64..96]].concat();
 let key=sender.chain_key.as_mut().ok_or("no sender chain key")?;key.key=state[96..128].to_vec();key.index=u32be(&state[128..132]);s.previous_counter=u32be(&state[132..136]);
 let old=s.receiver_chains.clone();if old.iter().any(|c|!c.message_keys.is_empty()){return Err("receiver skipped keys unsupported")}
 let mut next=vec![];let mut seen_empty=false;
 for slot in state[136..481].chunks_exact(69){
  if slot[0]==0{if !next.is_empty(){return Err("noncanonical empty receiver slot")}seen_empty=true;continue}
  if slot[0]!=255{return Err("noncanonical receiver validity")}
  let public=[&[5u8][..],&slot[1..33]].concat();
  if next.iter().any(|c:&storage::session_structure::Chain|c.sender_ratchet_key==public){return Err("duplicate receiver")}
  let mut c=old.iter().find(|c|c.sender_ratchet_key==public).cloned().unwrap_or_default();
  c.sender_ratchet_key=public;c.chain_key=Some(storage::session_structure::chain::ChainKey{index:u32be(&slot[65..69]),key:slot[33..65].to_vec()});next.push(c);
 }
 let _=seen_empty;s.receiver_chains=next;
 let mut pq=pqr::PqRatchetState::decode(s.pq_ratchet_state.as_slice()).map_err(|_|"PQ decode")?;
 let chain=pq.chain.as_mut().ok_or("PQ no chain")?;
 if chain.current_epoch.checked_add(1)!=Some(u64::from_be_bytes(state[481..489].try_into().unwrap()))||chain.links.len()!=1{return Err("PQ epoch/history unsupported")}
 let recv=chain.links[0].recv.as_mut().ok_or("PQ no receive chain")?;
 if !recv.prev.is_empty(){return Err("PQ skipped keys unsupported")}
 recv.next=state[489..521].to_vec();recv.ctr=u32be(&state[521..525]);s.pq_ratchet_state=pq.encode_to_vec();
 // Pinned tahini::on_receive_session_state / on_receive_active bookkeeping.
 if s.pending_pre_key.is_some() {
  s.pending_pre_key=None;s.pending_kyber_pre_key=None;
  if s.origin==storage::session_structure::Origin::LocalNew as i32{s.origin=storage::session_structure::Origin::LocalAcked as i32;}
 }
 let management=out.session_management_state.get_or_insert_with(||storage::record_structure::SessionManagementState::Tahini(Default::default()));
 match management {storage::record_structure::SessionManagementState::Tahini(t)=>t.last_act=storage::tahini_session_management_state::LastAct::ReceiveActive as i32};
 Ok(out)
}
pub fn apply_result(record:&storage::RecordStructure,result:&[u8])->Result<storage::RecordStructure,&'static str>{
 if result.len()!=608{return Err("receive result width")}
 match result[0]{0=>Ok(record.clone()),255=>apply_receive(record,&result[1..526]),_=>Err("noncanonical receive status")}
}

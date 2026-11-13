# OVHcloud Public Cloud (OpenStack API): one instance (Ubuntu 24.04) on the public network
# Ext-Net, its key pair, a security group (ssh from the administrators, WireGuard from anywhere,
# the monitoring page only if addresses are given) and the data disk attached. The host firewall
# (ufw) on the machine is the second layer. OVH VPS and dedicated servers are not created here:
# order them in OVH's panel and use provider = "existing".
terraform {
  required_providers {
    openstack = { source = "terraform-provider-openstack/openstack" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "size" { type = string }
variable "ssh_public_key" { type = string }
variable "admin_cidrs" { type = list(string) }
variable "monitoring_cidrs" { type = list(string) }
variable "disk_id" { type = string }
variable "device" { type = string }

resource "openstack_compute_keypair_v2" "admin" {
  name       = var.name
  public_key = var.ssh_public_key
  region     = var.region
}

resource "openstack_networking_secgroup_v2" "node" {
  name                 = var.name
  region               = var.region
  delete_default_rules = false
}

resource "openstack_networking_secgroup_rule_v2" "ssh" {
  for_each          = toset(var.admin_cidrs)
  region            = var.region
  security_group_id = openstack_networking_secgroup_v2.node.id
  direction         = "ingress"
  ethertype         = strcontains(each.value, ":") ? "IPv6" : "IPv4"
  protocol          = "tcp"
  port_range_min    = 22
  port_range_max    = 22
  remote_ip_prefix  = each.value
}

resource "openstack_networking_secgroup_rule_v2" "wireguard" {
  region            = var.region
  security_group_id = openstack_networking_secgroup_v2.node.id
  direction         = "ingress"
  ethertype         = "IPv4"
  protocol          = "udp"
  port_range_min    = 51820
  port_range_max    = 51820
  remote_ip_prefix  = "0.0.0.0/0"
}

resource "openstack_networking_secgroup_rule_v2" "page" {
  for_each          = toset(var.monitoring_cidrs)
  region            = var.region
  security_group_id = openstack_networking_secgroup_v2.node.id
  direction         = "ingress"
  ethertype         = strcontains(each.value, ":") ? "IPv6" : "IPv4"
  protocol          = "tcp"
  port_range_min    = 8088
  port_range_max    = 8088
  remote_ip_prefix  = each.value
}

resource "openstack_compute_instance_v2" "node" {
  name            = var.name
  region          = var.region
  image_name      = "Ubuntu 24.04"
  flavor_name     = var.size
  key_pair        = openstack_compute_keypair_v2.admin.name
  security_groups = [openstack_networking_secgroup_v2.node.name]
  network {
    name = "Ext-Net"
  }
}

resource "openstack_compute_volume_attach_v2" "data" {
  region      = var.region
  instance_id = openstack_compute_instance_v2.node.id
  volume_id   = var.disk_id
}

output "public_ip" { value = openstack_compute_instance_v2.node.access_ip_v4 }
output "device" { value = var.device }
output "ssh_user" { value = "ubuntu" }

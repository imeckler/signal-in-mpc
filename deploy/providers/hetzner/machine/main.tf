# Hetzner Cloud: one machine (Ubuntu 24.04), its ssh key, a provider firewall (ssh from the
# administrators, WireGuard from anywhere, the monitoring page only if addresses are given) and
# the data disk attached. The host firewall (ufw) on the machine is the second layer.
terraform {
  required_providers {
    hcloud = { source = "hetznercloud/hcloud" }
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

resource "hcloud_ssh_key" "admin" {
  name       = var.name
  public_key = var.ssh_public_key
}

resource "hcloud_firewall" "node" {
  name = var.name
  rule {
    direction  = "in"
    protocol   = "tcp"
    port       = "22"
    source_ips = var.admin_cidrs
  }
  rule {
    direction  = "in"
    protocol   = "udp"
    port       = "51820"
    source_ips = ["0.0.0.0/0", "::/0"]
  }
  rule {
    direction  = "in"
    protocol   = "icmp"
    source_ips = ["0.0.0.0/0", "::/0"]
  }
  dynamic "rule" {
    for_each = length(var.monitoring_cidrs) > 0 ? [1] : []
    content {
      direction  = "in"
      protocol   = "tcp"
      port       = "8088"
      source_ips = var.monitoring_cidrs
    }
  }
}

resource "hcloud_server" "node" {
  name         = var.name
  server_type  = var.size
  location     = var.region
  image        = "ubuntu-24.04"
  ssh_keys     = [hcloud_ssh_key.admin.id]
  firewall_ids = [hcloud_firewall.node.id]
  labels       = { "managed-by" = "tls-mpc-deploy" }
  public_net {
    ipv4_enabled = true
    ipv6_enabled = true
  }
}

resource "hcloud_volume_attachment" "data" {
  volume_id = tonumber(var.disk_id)
  server_id = hcloud_server.node.id
  automount = false
}

output "public_ip" { value = hcloud_server.node.ipv4_address }
output "device" { value = var.device }
output "ssh_user" { value = "root" }

# UpCloud: one machine (Ubuntu 24.04) with the data disk attached, and its firewall (ssh from the
# administrators, WireGuard from anywhere, the monitoring page only if addresses are given;
# everything else dropped). The host firewall (ufw) on the machine is the second layer.
terraform {
  required_providers {
    upcloud = { source = "UpCloudLtd/upcloud" }
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

resource "upcloud_server" "node" {
  hostname = var.name
  title    = var.name
  zone     = var.region
  plan     = var.size
  firewall = true
  metadata = true

  template {
    storage = "Ubuntu Server 24.04 LTS (Noble Numbat)"
    size    = 50
  }

  storage_devices {
    storage = var.disk_id
    type    = "disk"
  }

  network_interface {
    type = "public"
  }

  login {
    user = "root"
    keys = [var.ssh_public_key]
  }
}

locals {
  admin_v4 = [for c in var.admin_cidrs : c if !strcontains(c, ":")]
}

resource "upcloud_firewall_rules" "node" {
  server_id = upcloud_server.node.id

  dynamic "firewall_rule" {
    for_each = local.admin_v4
    content {
      action                    = "accept"
      direction                 = "in"
      family                    = "IPv4"
      protocol                  = "tcp"
      destination_port_start    = "22"
      destination_port_end      = "22"
      source_address_start      = cidrhost(firewall_rule.value, 0)
      source_address_end        = cidrhost(firewall_rule.value, -1)
    }
  }
  firewall_rule {
    action                 = "accept"
    direction              = "in"
    family                 = "IPv4"
    protocol               = "udp"
    destination_port_start = "51820"
    destination_port_end   = "51820"
  }
  dynamic "firewall_rule" {
    for_each = [for c in var.monitoring_cidrs : c if !strcontains(c, ":")]
    content {
      action                 = "accept"
      direction              = "in"
      family                 = "IPv4"
      protocol               = "tcp"
      destination_port_start = "8088"
      destination_port_end   = "8088"
      source_address_start   = cidrhost(firewall_rule.value, 0)
      source_address_end     = cidrhost(firewall_rule.value, -1)
    }
  }
  firewall_rule {
    action    = "drop"
    direction = "in"
  }
}

output "public_ip" { value = upcloud_server.node.network_interface[0].ip_address }
output "device" { value = var.device }
output "ssh_user" { value = "root" }

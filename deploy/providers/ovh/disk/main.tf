# OVHcloud Public Cloud (OpenStack API): one data disk (block storage volume) for a node, kept by
# `deploy.py destroy` unless --delete-data. Unformatted: the node formats it only if blank.
terraform {
  required_providers {
    openstack = { source = "terraform-provider-openstack/openstack" }
  }
}

variable "name" { type = string }
variable "region" { type = string }
variable "size_gb" { type = number }

resource "openstack_blockstorage_volume_v3" "data" {
  name        = var.name
  size        = var.size_gb
  region      = var.region
  volume_type = "classic"
}

output "disk_id" { value = openstack_blockstorage_volume_v3.data.id }
# Virtio disk ids carry the first 20 characters of the volume id.
output "device" { value = "/dev/disk/by-id/virtio-${substr(openstack_blockstorage_volume_v3.data.id, 0, 20)}" }

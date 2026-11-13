# A "machine" of the `local` provider: a container that stands in for a freshly created Ubuntu
# 24.04 server reachable over ssh (as the `existing` provider expects). It runs systemd and sshd
# and nothing else: Docker, WireGuard, the firewall and every service are installed by the same
# Ansible roles as on a cloud machine. Started privileged (WireGuard, nftables and the nested
# Docker need it) by deploy/pushbutton/local.py. TEST ONLY: never a production machine.
FROM ubuntu:noble
ENV DEBIAN_FRONTEND=noninteractive container=docker
RUN set -eux; apt-get update; \
    apt-get install -y --no-install-recommends systemd systemd-sysv dbus openssh-server python3 sudo \
        iproute2 iputils-ping ca-certificates curl gnupg kmod udev; \
    rm -rf /var/lib/apt/lists/*; \
    mkdir -p /run/sshd /root/.ssh; chmod 700 /root/.ssh; \
    sed -i 's/^#\?PermitRootLogin.*/PermitRootLogin prohibit-password/; s/^#\?PasswordAuthentication.*/PasswordAuthentication no/' /etc/ssh/sshd_config; \
    systemctl enable ssh; \
    systemctl mask systemd-logind.service getty.target console-getty.service systemd-udevd.service systemd-udev-trigger.service || true; \
    rm -f /etc/ssh/ssh_host_*; \
    printf '[Unit]\nDescription=ssh host keys\nBefore=ssh.service\n[Service]\nType=oneshot\nExecStart=/usr/bin/ssh-keygen -A\n[Install]\nWantedBy=multi-user.target\n' > /etc/systemd/system/ssh-hostkeys.service; \
    systemctl enable ssh-hostkeys.service; \
    printf '[Unit]\nDescription=authorized key from the deploy tool\nBefore=ssh.service\nConditionPathExists=/etc/pb-authorized_key\n[Service]\nType=oneshot\nExecStart=/bin/sh -c "install -m 600 /etc/pb-authorized_key /root/.ssh/authorized_keys"\n[Install]\nWantedBy=multi-user.target\n' > /etc/systemd/system/pb-authorized-key.service; \
    systemctl enable pb-authorized-key.service
STOPSIGNAL SIGRTMIN+3
CMD ["/sbin/init"]

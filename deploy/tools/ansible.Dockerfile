# The Ansible the deploy tool runs (deploy/deploy.py builds this image once and tags it
# tls-mpc-deploy-ansible:VERSION). Nothing secret is in the image; the deployment's state
# directory and its ssh key are mounted at run time.
#
#   docker build -f deploy/tools/ansible.Dockerfile -t tls-mpc-deploy-ansible:1 deploy/tools
FROM python:3.12.8-slim-bookworm
ENV DEBIAN_FRONTEND=noninteractive PIP_NO_CACHE_DIR=1 PIP_DISABLE_PIP_VERSION_CHECK=1
RUN set -eux; apt-get update; \
    apt-get install -y --no-install-recommends openssh-client rsync git; \
    rm -rf /var/lib/apt/lists/*
RUN set -eux; pip install ansible-core==2.17.7 ansible-lint==24.12.2; \
    ansible-galaxy collection install --collections-path /usr/share/ansible/collections \
        ansible.posix:1.6.2 community.general:9.5.2 community.docker:4.1.0
ENV ANSIBLE_COLLECTIONS_PATH=/usr/share/ansible/collections \
    ANSIBLE_HOST_KEY_CHECKING=False ANSIBLE_RETRY_FILES_ENABLED=False \
    ANSIBLE_STDOUT_CALLBACK=default ANSIBLE_NOCOLOR=1 ANSIBLE_FORCE_COLOR=0
WORKDIR /work

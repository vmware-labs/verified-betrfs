FROM ubuntu:latest
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -y ca-certificates gnupg2
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF
COPY assets/mono-official-stable.list /etc/apt/sources.list.d/
RUN apt-get update
RUN useradd -ms /bin/bash dafnyserver
RUN apt-get install -y mono-runtime mono-mcs mono-devel git make wget unzip ssh
RUN apt-get install -y vim emacs
RUN apt-get install -y python3-pip
FROM ubuntu:latest
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -y ca-certificates gnupg2
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF
COPY assets/mono-official-stable.list /etc/apt/sources.list.d/
RUN apt-get update
RUN useradd -ms /bin/bash dafnyserver
RUN apt-get install -y mono-runtime mono-mcs mono-devel git make wget unzip ssh
RUN apt-get install -y vim emacs
RUN apt-get install -y python3-pip
RUN pip3 install toposort
COPY assets/etc-ssh /etc/ssh/
COPY --chown=dafnyserver assets/dot-ssh /home/dafnyserver/.ssh
RUN update-rc.d ssh defaults
RUN sed -i 's/SSHD_OPTS=/SSHD_OPTS=-D/' /etc/default/ssh
WORKDIR /home/dafnyserver
COPY --chown=dafnyserver assets/veribetrfs veribetrfs
WORKDIR /home/dafnyserver/veribetrfs
RUN tools/install-dafny.sh
CMD ["/etc/init.d/ssh", "start"]

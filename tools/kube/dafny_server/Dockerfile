FROM ubuntu:latest

# https://askubuntu.com/questions/909277/avoiding-user-interaction-with-tzdata-when-installing-certbot-in-a-docker-contai
ARG DEBIAN_FRONTEND=noninteractive

# Load mono keys so we can install PPA to get a recent version (ubuntu ships
# with 4.x; we want 6.x)
RUN apt-get update
RUN apt-get install -y ca-certificates gnupg2
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF

# Now install mono and goodies.
COPY mono-official-stable.list /etc/apt/sources.list.d/
# https://gist.github.com/dergachev/8441335
RUN apt-get update
RUN useradd -ms /bin/bash dafnyserver
RUN apt-get install -y mono-runtime mono-mcs mono-devel git make wget unzip
USER dafnyserver
WORKDIR /home/dafnyserver
#RUN git clone https://github.com/secure-foundations/dafny.git
COPY install-dafny.sh /home/dafnyserver
RUN ./install-dafny.sh
COPY test.dfy /home/dafnyserver
RUN mkdir bin
#RUN ln -s /home/dafnyserver/.dafny/dafny/Binaries/dafny bin/dafny
COPY bin_dafny_sh bin/dafny
COPY bin_dafny_exe_sh bin/dafny_exe
COPY bashrc-appendage /tmp
RUN cat /tmp/bashrc-appendage >> /home/dafnyserver/.bashrc

# veribetrfs dafny server
# current dafny; ssh keys
WORKDIR /home/dafnyserver
RUN git clone git@github.com:splatlab/veribetrfs.git
WORKDIR /home/dafnyserver/veribetrfs
RUN tools/install-dafny.sh

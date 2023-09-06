FROM debian:stable-20220912-slim

# Install OpenJDK 11
RUN apt-get update \
    && apt-get install openjdk-11-jdk-headless -y \
    && export JAVA_HOME=/usr/lib/jvm/openjdk-11-jdk \
    && export PATH=$PATH:$JAVA_HOME/bin

# Install dependencies for SBT install
RUN apt-get update \
    && apt-get install curl -y \
    && apt-get install gnupg -y

# Setup repository to install SBT from
RUN curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | gpg --dearmor > /usr/share/keyrings/scala-sbt.gpg \
    && echo "deb [signed-by=/usr/share/keyrings/scala-sbt.gpg] https://repo.scala-sbt.org/scalasbt/debian all main" | tee /etc/apt/sources.list.d/sbt.list \
    && echo "deb [signed-by=/usr/share/keyrings/scala-sbt.gpg] https://repo.scala-sbt.org/scalasbt/debian /" | tee /etc/apt/sources.list.d/sbt_old.list

# Install SBT
RUN apt-get update \
    && apt-get install sbt -y

# Install python dependencies for EFSM inference tool
RUN apt-get update \
    && apt-get install python3 -y \
    && apt-get install libpython3.9 -y \
    && apt-get install libenchant-2-2 -y \
    && apt-get install python3-pip -y \
    && apt-get install graphviz -y
COPY inference-tool/requirements.txt /root
RUN pip install -r /root/requirements.txt

# Install further dependencies for EFSM inference tool
RUN apt-get update \
    && apt-get install libz3-java -y

# Add and use non-root user in the container
RUN useradd sbtuser \
    && mkdir -p /home/sbtuser/efsm-inference \
    && chown -R sbtuser:sbtuser /home/sbtuser \
    && cd /home/sbtuser

# Setup user and working directory
USER sbtuser:sbtuser
WORKDIR /home/sbtuser

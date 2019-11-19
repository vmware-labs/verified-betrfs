FROM mcr.microsoft.com/dotnet/core/sdk:2.2

RUN apt-get update -y
RUN apt-get install -y make linux-tools

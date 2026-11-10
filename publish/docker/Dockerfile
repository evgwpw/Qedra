# syntax=docker/dockerfile:1
# Qedra MCP server over stdio. Build context: repository root.
FROM mcr.microsoft.com/dotnet/sdk:10.0 AS build
WORKDIR /src
COPY Directory.Build.props Lisp.slnx ./
COPY src/ src/
COPY lib/ lib/
RUN dotnet publish src/Lisp.Host/Lisp.Host.fsproj -c Release -r linux-x64 --self-contained true \
      -o /app -nologo -p:DebugType=None -p:DebugSymbols=false \
 && cp /app/Lisp /app/qedra

FROM mcr.microsoft.com/dotnet/runtime-deps:10.0
ARG VERSION=1.109.7.11
LABEL io.modelcontextprotocol.server.name="io.github.evgwpw/qedra" \
      org.opencontainers.image.title="Qedra" \
      org.opencontainers.image.description="Computer algebra with verifiable answers" \
      org.opencontainers.image.source="https://github.com/evgwpw/Qedra" \
      org.opencontainers.image.licenses="0BSD" \
      org.opencontainers.image.version="${VERSION}"

WORKDIR /app
COPY --from=build /app ./
COPY LICENSE README.md README.en.md THIRD-PARTY-NOTICES.md ./
RUN useradd -r -u 10001 qedra && chown -R qedra:qedra /app
USER qedra

ENTRYPOINT ["/app/qedra", "--mcp"]

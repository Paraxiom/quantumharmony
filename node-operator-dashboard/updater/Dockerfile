FROM alpine:3.19
RUN apk add --no-cache curl jq docker-cli docker-compose
COPY check-update.sh /check-update.sh
RUN chmod +x /check-update.sh
ENTRYPOINT ["/check-update.sh"]

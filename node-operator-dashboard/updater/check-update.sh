#!/bin/sh
# QuantumHarmony Auto-Update & Uptime Agent
# - Checks Docker Hub for new images once per day
# - Monitors node health every 60s, restarts if down
# - Rolls back to previous image on failed update

IMAGE="${IMAGE:-sylvaincormier/quantumharmony-node}"
TAG="${IMAGE_TAG:-arm64}"
UPDATE_INTERVAL="${UPDATE_INTERVAL:-86400}"   # 24 hours between image checks
MONITOR_INTERVAL="${MONITOR_INTERVAL:-60}"    # 60s between health pings
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-180}"       # 3 minutes for node to start
HEALTH_URL="${HEALTH_URL:-http://node:9944/health}"
COMPOSE_FILE="${COMPOSE_FILE:-/compose/docker-compose.yml}"
COMPOSE_PROJECT="${COMPOSE_PROJECT:-node-operator-dashboard}"
NODE_CONTAINER="${NODE_CONTAINER:-quantumharmony-node}"

get_remote_digest() {
  TOKEN=$(curl -sf "https://auth.docker.io/token?service=registry.docker.io&scope=repository:${IMAGE}:pull" | jq -r '.token')
  if [ -z "$TOKEN" ] || [ "$TOKEN" = "null" ]; then
    return 1
  fi
  curl -sf -H "Authorization: Bearer $TOKEN" \
    -H "Accept: application/vnd.docker.distribution.manifest.v2+json" \
    "https://registry-1.docker.io/v2/${IMAGE}/manifests/${TAG}" \
    -o /dev/null -D - 2>/dev/null | grep -i docker-content-digest | awk '{print $2}' | tr -d '\r'
}

get_local_digest() {
  docker image inspect "${IMAGE}:${TAG}" --format='{{index .RepoDigests 0}}' 2>/dev/null | cut -d@ -f2
}

wait_for_health() {
  local elapsed=0
  while [ $elapsed -lt "$HEALTH_TIMEOUT" ]; do
    if curl -sf "$HEALTH_URL" > /dev/null 2>&1; then
      return 0
    fi
    sleep 10
    elapsed=$((elapsed + 10))
    echo "[updater] Waiting for node health... ${elapsed}s/${HEALTH_TIMEOUT}s"
  done
  return 1
}

restart_node() {
  echo "[updater] Stopping container..."
  docker stop "$NODE_CONTAINER" 2>/dev/null
  docker rm "$NODE_CONTAINER" 2>/dev/null
  echo "[updater] Starting node..."
  docker compose -f "$COMPOSE_FILE" -p "$COMPOSE_PROJECT" up -d --no-deps node
}

echo "[updater] ================================================"
echo "[updater] QuantumHarmony Auto-Update & Uptime Agent"
echo "[updater] ================================================"
echo "[updater] Image: ${IMAGE}:${TAG}"
echo "[updater] Image check interval: ${UPDATE_INTERVAL}s ($(( UPDATE_INTERVAL / 3600 ))h)"
echo "[updater] Health monitor interval: ${MONITOR_INTERVAL}s"
echo "[updater] Health timeout: ${HEALTH_TIMEOUT}s"
echo "[updater] Health URL: ${HEALTH_URL}"
echo "[updater] Node container: ${NODE_CONTAINER}"

LOCAL_DIGEST=$(get_local_digest)
echo "[updater] Current digest: ${LOCAL_DIGEST:-unknown}"
echo "[updater] Entering monitor loop..."

LAST_UPDATE_CHECK=0
CONSECUTIVE_FAILURES=0

while true; do
  sleep "$MONITOR_INTERVAL"
  NOW=$(date +%s)

  # --- Uptime monitor: check node health every cycle ---
  if ! curl -sf "$HEALTH_URL" > /dev/null 2>&1; then
    CONSECUTIVE_FAILURES=$((CONSECUTIVE_FAILURES + 1))
    echo "[monitor] $(date '+%Y-%m-%d %H:%M:%S') Node unhealthy (${CONSECUTIVE_FAILURES}/3)"

    if [ "$CONSECUTIVE_FAILURES" -ge 3 ]; then
      echo "[monitor] Node down for 3 consecutive checks, restarting..."
      restart_node

      if wait_for_health; then
        echo "[monitor] Node recovered after restart"
      else
        echo "[monitor] CRITICAL: Node failed to recover after restart"
      fi
      CONSECUTIVE_FAILURES=0
    fi
  else
    if [ "$CONSECUTIVE_FAILURES" -gt 0 ]; then
      echo "[monitor] $(date '+%Y-%m-%d %H:%M:%S') Node recovered"
    fi
    CONSECUTIVE_FAILURES=0
  fi

  # --- Image update check: once per UPDATE_INTERVAL ---
  ELAPSED_SINCE_CHECK=$((NOW - LAST_UPDATE_CHECK))
  if [ "$ELAPSED_SINCE_CHECK" -lt "$UPDATE_INTERVAL" ]; then
    continue
  fi
  LAST_UPDATE_CHECK=$NOW

  echo "[updater] $(date '+%Y-%m-%d %H:%M:%S') Checking for image updates..."
  REMOTE_DIGEST=$(get_remote_digest)
  LOCAL_DIGEST=$(get_local_digest)

  if [ -z "$REMOTE_DIGEST" ]; then
    echo "[updater] WARNING: Could not fetch remote digest, will retry next cycle"
    continue
  fi

  if [ "$REMOTE_DIGEST" = "$LOCAL_DIGEST" ]; then
    echo "[updater] No update available"
    continue
  fi

  echo "[updater] ================================================"
  echo "[updater] $(date '+%Y-%m-%d %H:%M:%S') NEW IMAGE DETECTED"
  echo "[updater] Local:  ${LOCAL_DIGEST}"
  echo "[updater] Remote: ${REMOTE_DIGEST}"
  echo "[updater] ================================================"

  echo "[updater] Pulling new image..."
  if ! docker pull "${IMAGE}:${TAG}"; then
    echo "[updater] ERROR: Pull failed, skipping update"
    continue
  fi

  OLD_IMAGE=$(docker inspect "$NODE_CONTAINER" --format='{{.Image}}' 2>/dev/null)

  restart_node

  echo "[updater] Running health check (timeout: ${HEALTH_TIMEOUT}s)..."
  if wait_for_health; then
    echo "[updater] UPDATE SUCCESSFUL - node healthy with new image"
    docker image prune -f > /dev/null 2>&1
  else
    echo "[updater] ERROR: Node unhealthy after update, rolling back..."
    if [ -n "$OLD_IMAGE" ]; then
      docker tag "$OLD_IMAGE" "${IMAGE}:${TAG}"
      restart_node
      echo "[updater] Rollback initiated, waiting for health..."
      if wait_for_health; then
        echo "[updater] Rollback successful - node healthy on previous image"
      else
        echo "[updater] CRITICAL: Rollback also failed! Manual intervention required."
      fi
    else
      echo "[updater] ERROR: No previous image ID available for rollback"
    fi
  fi
done

#!/bin/sh
# Automated backup script for QuantumHarmony governance data

BACKUP_DIR="/backups"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
DB_HOST="postgres"
DB_NAME="governance"
DB_USER="quantum"
DB_PASS="quantum_harmony_secure_2025"

# Create backup directory if it doesn't exist
mkdir -p ${BACKUP_DIR}/daily
mkdir -p ${BACKUP_DIR}/weekly
mkdir -p ${BACKUP_DIR}/monthly

echo "Starting backup at ${TIMESTAMP}"

# Daily backup
PGPASSWORD=${DB_PASS} pg_dump -h ${DB_HOST} -U ${DB_USER} -d ${DB_NAME} -f ${BACKUP_DIR}/daily/governance_${TIMESTAMP}.sql

# Keep only last 7 daily backups
find ${BACKUP_DIR}/daily -name "*.sql" -mtime +7 -delete

# Weekly backup (every Sunday)
if [ $(date +%u) -eq 7 ]; then
    cp ${BACKUP_DIR}/daily/governance_${TIMESTAMP}.sql ${BACKUP_DIR}/weekly/
    find ${BACKUP_DIR}/weekly -name "*.sql" -mtime +30 -delete
fi

# Monthly backup (first day of month)
if [ $(date +%d) -eq 01 ]; then
    cp ${BACKUP_DIR}/daily/governance_${TIMESTAMP}.sql ${BACKUP_DIR}/monthly/
    find ${BACKUP_DIR}/monthly -name "*.sql" -mtime +365 -delete
fi

echo "Backup completed at $(date)"
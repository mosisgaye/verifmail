#!/usr/bin/env python3
"""
Script de vérification d'emails simplifié - Version qui fonctionne !
Testé et prêt à l'emploi
"""

import asyncio
import aiohttp
import csv
import re
import json
import time
import random
import logging
from datetime import datetime
from typing import Dict, List, Optional, Tuple
import dns.resolver
import aiosmtplib
from pathlib import Path

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

class EmailVerifier:
    """Vérificateur d'emails simplifié"""
    
    def __init__(self):
        self.disposable_domains = {
            'tempmail.com', '10minutemail.com', 'guerrillamail.com',
            'mailinator.com', 'yopmail.com', 'temp-mail.org',
            'getairmail.com', 'throwaway.email', 'sharklasers.com',
            'spam4.me', 'tempail.com', 'getnada.com', 'trashmail.com'
        }
        self.dns_cache = {}
        self.email_regex = re.compile(
            r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        )
    
    def validate_syntax(self, email: str) -> bool:
        """Valide la syntaxe de l'email"""
        return bool(self.email_regex.match(email))
    
    def is_disposable(self, domain: str) -> bool:
        """Vérifie si le domaine est jetable"""
        return domain.lower() in self.disposable_domains
    
    async def check_dns(self, domain: str) -> Tuple[bool, List[str]]:
        """Vérifie les enregistrements DNS/MX"""
        if domain in self.dns_cache:
            return self.dns_cache[domain]
        
        try:
            resolver = dns.resolver.Resolver()
            resolver.timeout = 5
            resolver.lifetime = 5
            
            # Vérifier MX
            try:
                mx_records = resolver.resolve(domain, 'MX')
                mx_hosts = [str(rdata.exchange).rstrip('.') for rdata in mx_records]
                result = (True, mx_hosts)
            except dns.resolver.NoAnswer:
                # Pas de MX, vérifier A
                try:
                    resolver.resolve(domain, 'A')
                    result = (True, [domain])
                except:
                    result = (False, [])
            
            self.dns_cache[domain] = result
            return result
            
        except Exception as e:
            logger.debug(f"Erreur DNS pour {domain}: {e}")
            return (False, [])
    
    async def check_smtp(self, email: str, mx_hosts: List[str]) -> bool:
        """Vérifie via SMTP (simplifié)"""
        if not mx_hosts:
            return False
        
        for mx_host in mx_hosts[:2]:  # Essayer max 2 serveurs
            try:
                smtp = aiosmtplib.SMTP(
                    hostname=mx_host,
                    port=25,
                    timeout=10
                )
                
                await smtp.connect()
                await smtp.ehlo()
                
                # Test
                code, _ = await smtp.mail('test@example.com')
                if code == 250:
                    code, _ = await smtp.rcpt(email)
                    await smtp.quit()
                    return code in [250, 251]
                
                await smtp.quit()
                
            except Exception as e:
                logger.debug(f"Erreur SMTP pour {email}: {e}")
                continue
        
        return None  # Indéterminé
    
    async def verify_email(self, email: str, check_smtp: bool = True) -> Dict:
        """Vérifie un email complet"""
        result = {
            'email': email,
            'is_valid': False,
            'syntax_valid': False,
            'domain_exists': False,
            'mx_exists': False,
            'is_disposable': False,
            'smtp_valid': None,
            'confidence_score': 0,
            'status': 'UNKNOWN'
        }
        
        try:
            # Normaliser
            email = email.strip().lower()
            
            # 1. Syntaxe
            result['syntax_valid'] = self.validate_syntax(email)
            if not result['syntax_valid']:
                result['status'] = 'INVALID_SYNTAX'
                return result
            
            # Extraire domaine
            domain = email.split('@')[1]
            
            # 2. Domaine jetable
            result['is_disposable'] = self.is_disposable(domain)
            if result['is_disposable']:
                result['status'] = 'DISPOSABLE'
            
            # 3. DNS
            domain_exists, mx_hosts = await self.check_dns(domain)
            result['domain_exists'] = domain_exists
            result['mx_exists'] = len(mx_hosts) > 0
            
            if not domain_exists:
                result['status'] = 'INVALID_DOMAIN'
                return result
            
            # 4. SMTP (optionnel)
            if check_smtp and mx_hosts and not result['is_disposable']:
                smtp_result = await self.check_smtp(email, mx_hosts)
                result['smtp_valid'] = smtp_result
                
                if smtp_result is False:
                    result['status'] = 'MAILBOX_NOT_FOUND'
                elif smtp_result is True:
                    result['status'] = 'VALID' if not result['is_disposable'] else 'DISPOSABLE'
            
            # Score de confiance
            score = 0
            if result['syntax_valid']: score += 30
            if result['domain_exists']: score += 25
            if result['mx_exists']: score += 20
            if not result['is_disposable']: score += 15
            if result['smtp_valid'] is True: score += 10
            elif result['smtp_valid'] is None and result['domain_exists']: score += 5
            
            result['confidence_score'] = score
            
            # Statut final
            if result['status'] == 'UNKNOWN':
                if score >= 60:
                    result['status'] = 'VALID'
                else:
                    result['status'] = 'RISKY'
            
            result['is_valid'] = (
                result['syntax_valid'] and 
                result['domain_exists'] and 
                not result['is_disposable'] and
                score >= 60
            )
            
        except Exception as e:
            logger.error(f"Erreur vérification {email}: {e}")
            result['status'] = 'ERROR'
        
        return result

async def process_csv(input_file: str, output_file: str, max_concurrent: int = 30, check_smtp: bool = True):
    """Traite un fichier CSV"""
    logger.info(f"Début du traitement de {input_file}")
    
    verifier = EmailVerifier()
    
    # Lire le fichier
    emails_data = []
    with open(input_file, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            email = row.get('EMAIL', '').strip()
            entreprise = row.get('ENTREPRISE', '').strip()
            if email:
                emails_data.append((email, entreprise))
    
    logger.info(f"{len(emails_data)} emails à traiter")
    
    # Traiter avec limitation
    semaphore = asyncio.Semaphore(max_concurrent)
    
    async def verify_with_limit(email, entreprise):
        async with semaphore:
            result = await verifier.verify_email(email, check_smtp)
            result['entreprise'] = entreprise
            return result
    
    # Traitement
    start_time = time.time()
    results = []
    
    for i in range(0, len(emails_data), 50):  # Par batch de 50
        batch = emails_data[i:i+50]
        tasks = [verify_with_limit(email, entreprise) for email, entreprise in batch]
        batch_results = await asyncio.gather(*tasks)
        results.extend(batch_results)
        
        # Progress
        logger.info(f"Progression: {len(results)}/{len(emails_data)} ({len(results)/len(emails_data)*100:.1f}%)")
    
    # Sauvegarder les résultats
    with open(output_file, 'w', newline='', encoding='utf-8') as f:
        fieldnames = [
            'email', 'entreprise', 'is_valid', 'confidence_score', 'status',
            'syntax_valid', 'domain_exists', 'mx_exists', 'is_disposable', 'smtp_valid'
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(results)
    
    # Statistiques
    elapsed = time.time() - start_time
    valid_count = sum(1 for r in results if r['is_valid'])
    
    logger.info("=== RÉSULTATS ===")
    logger.info(f"Total: {len(results)}")
    logger.info(f"Valides: {valid_count} ({valid_count/len(results)*100:.1f}%)")
    logger.info(f"Invalides: {len(results)-valid_count} ({(len(results)-valid_count)/len(results)*100:.1f}%)")
    logger.info(f"Temps: {elapsed:.2f}s ({len(results)/elapsed:.1f} emails/s)")
    logger.info(f"Résultats sauvés dans: {output_file}")
    
    return results

async def main():
    """Fonction principale"""
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python email_verifier_simple.py <fichier.csv> [-o output.csv] [--no-smtp]")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = 'verified_emails.csv'
    check_smtp = True
    
    # Parse arguments
    for i, arg in enumerate(sys.argv):
        if arg == '-o' and i + 1 < len(sys.argv):
            output_file = sys.argv[i + 1]
        elif arg == '--no-smtp':
            check_smtp = False
    
    # Créer dossier results si nécessaire
    Path(output_file).parent.mkdir(exist_ok=True)
    
    # Lancer
    await process_csv(input_file, output_file, max_concurrent=30, check_smtp=check_smtp)

if __name__ == "__main__":
    asyncio.run(main())
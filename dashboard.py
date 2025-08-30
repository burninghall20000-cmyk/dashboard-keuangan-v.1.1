#!/usr/bin/env python3
"""
Simple Subdomain Scanner + Wayback History
Author: AI Assistant
"""

import re, requests, os, json, time, threading, dns.resolver
from concurrent.futures import ThreadPoolExecutor, as_completed
from rich.console import Console
from rich.table import Table

console = Console()
RESULT_FOLDER = "results"
os.makedirs(RESULT_FOLDER, exist_ok=True)
SUMMARY_FILE = os.path.join(RESULT_FOLDER, "all_live_subdomains.txt")
thread_local = threading.local()

# ==== Session ====
def get_session():
    if not hasattr(thread_local, "session"):
        session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(pool_connections=100, pool_maxsize=200)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.headers.update({"User-Agent": "Mozilla/5.0"})
        thread_local.session = session
    return thread_local.session

def fetch(url, timeout=5):
    try: return get_session().get(url, timeout=timeout).text
    except: return ""

# ==== Clean subdomain ====
def clean_sub(sub, domain):
    sub = sub.lower().strip()
    sub = re.sub(r"^\*\.", "", sub)
    sub = re.sub(r"^\.+|\.+$", "", sub)
    if sub.endswith(f".{domain}"): return sub
    return None

# ==== DNS ====
def setup_resolver():
    r = dns.resolver.Resolver(configure=False)
    r.nameservers = ["8.8.8.8","1.1.1.1","8.8.4.4","1.0.0.1"]
    r.timeout = 1; r.lifetime = 1
    return r

def dns_resolve(sub, r):
    try:
        for t in ["A","CNAME","AAAA","MX"]:
            try:
                ans = r.resolve(sub, t, raise_on_no_answer=False)
                if ans.rrset: return True
            except: continue
    except: return False
    return False

# ==== Sources ====
def crtsh(domain):
    subs=set(); text=fetch(f"https://crt.sh/?q=%25.{domain}&output=json")
    try:
        for item in json.loads(text):
            for f in ["name_value","common_name"]:
                for v in str(item.get(f,"")).split("\n"):
                    c=clean_sub(v,domain); 
                    if c: subs.add(c)
    except: pass
    return subs

def rapiddns(domain):
    subs=set(); text=fetch(f"https://rapiddns.io/subdomain/{domain}?full=1")
    for m in re.findall(rf">([a-z0-9._-]+\.{re.escape(domain)})<", text, re.I):
        c=clean_sub(m,domain); 
        if c: subs.add(c)
    return subs

def jldc(domain):
    subs=set(); text=fetch(f"https://jldc.me/anubis/subdomains/{domain}")
    try:
        for v in json.loads(text):
            c=clean_sub(v,domain); 
            if c: subs.add(c)
    except: pass
    return subs

def threatcrowd(domain):
    subs=set(); text=fetch(f"https://www.threatcrowd.org/searchApi/v2/domain/report/?domain={domain}")
    try:
        for v in json.loads(text).get("subdomains",[]):
            c=clean_sub(v,domain); 
            if c: subs.add(c)
    except: pass
    return subs

SOURCES=[crtsh,rapiddns,jldc,threatcrowd]

# ==== Probe + Wayback ====
def probe(sub, resolver):
    if dns_resolve(sub,resolver):
        for scheme in ["https://","http://"]:
            try:
                r=get_session().head(f"{scheme}{sub}",timeout=3,allow_redirects=True)
                if r.status_code<400: return f"{scheme}{sub}"
            except: continue
    return None

def wayback(sub,years=2):
    try:
        url=f"http://archive.org/wayback/available?url={sub}"
        data=get_session().get(url,timeout=5).json()
        snap=data.get("archived_snapshots",{}).get("closest",{})
        if snap:
            ts=snap.get("timestamp")
            if ts and int(ts[:4])>=int(time.strftime("%Y"))-years:
                return snap.get("url")
    except: pass
    return None

# ==== Main scan ====
def scan(domain):
    console.print(f"[cyan]Scanning {domain}...[/cyan]")
    resolver=setup_resolver()
    allsubs=set()

    # collect
    with ThreadPoolExecutor(max_workers=len(SOURCES)) as ex:
        fut={ex.submit(s,domain):s.__name__ for s in SOURCES}
        for f in as_completed(fut): allsubs.update(f.result())

    console.print(f"Collected: {len(allsubs)} subdomains")
    results=[]

    # probe
    with ThreadPoolExecutor(max_workers=50) as ex:
        fut={ex.submit(probe,s,resolver):s for s in allsubs}
        for f in as_completed(fut):
            sub=fut[f]; live=f.result(); wb=None; status="Dead"
            if live: status="Live"; wb=wayback(live)
            results.append((sub,live,status,wb))

    # output table
    table=Table(title=f"Results for {domain}")
    table.add_column("#"); table.add_column("Subdomain"); table.add_column("Status"); table.add_column("Wayback")
    for i,(sub,live,status,wb) in enumerate(sorted(results),1):
        table.add_row(str(i),live or sub,status,wb or "-")
    console.print(table)

    # save live
    lives=[live for _,live,s,_ in results if live]
    with open(os.path.join(RESULT_FOLDER,f"{domain}.txt"),"w") as f:
        [f.write(l+"\n") for l in sorted(lives)]
    with open(SUMMARY_FILE,"a") as f:
        [f.write(l+"\n") for l in lives]

def main():
    if not os.path.exists("domains.txt"):
        console.print("[red]File domains.txt not found![/red]"); return
    if os.path.exists(SUMMARY_FILE): os.remove(SUMMARY_FILE)
    domains=[re.sub(r"^https?://(www\.)?|^www\.","",d.strip()) for d in open("domains.txt") if d.strip()]
    for d in domains: scan(d)

if __name__=="__main__": main()

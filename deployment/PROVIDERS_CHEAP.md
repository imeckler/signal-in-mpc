# Cheaper hosting for the two computation nodes and five database nodes

Date of research: 11 November 2026. Prices exclude VAT. This report follows on from `PROVIDERS.md` (same date, latency-first) and reuses its measurements where they still apply. The priorities here are, in order: jurisdiction, throughput, cost, and latency only as a soft limit (below about 20 ms).

## How to read this report

- **Measured today.** Round-trip times were taken on 11 Nov 2026 between 23:00 and 23:10 UTC with the public Globalping network (https://globalping.io): a probe inside provider A sent 8 ICMP pings to a public test host of provider B. Raw rows with measurement IDs are in Appendix A. They are one late-evening snapshot to test hosts, not to rented servers.
- **Fetched today.** A price or wording with a URL was read from that page today. OVHcloud prices marked "catalogue" come from OVHcloud's public order catalogue (`https://eu.api.ovh.com/1.0/order/catalog/public/{eco,vps,cloud}?ovhSubsidiary=IE`), which is what the order form uses.
- **Not verified.** Scaleway, UpCloud and Leaseweb pricing pages refused automated fetches again (HTTP 403). Infomaniak's and Exoscale's price pages render prices with scripts and returned none. Hetzner's server-auction list could not be read (the page loads it with scripts and the data address returned 404). Where I rely on a third-party listing or a search snippet, the line says so.
- **No throughput was measured.** Nothing in this report shows that any path carries multi-gigabit flows. That can only be established by renting both machines and running iperf3 (section 8).

## Summary

1. **Nothing found beats the current Helsinki + Tallinn plan on jurisdiction, port speed and latency at once.** It is the only pair with 10 Gbit/s ports at both ends, both data centres outside the intelligence-sharing groupings, and a 2.1 ms round trip. Every cheaper pair gives up something on the first two criteria.
2. **The cheapest sound change is Hetzner (Germany) + OVHcloud (Strasbourg, France).** Measured 6.2–7.2 ms from Nuremberg and 7.8–8.8 ms from Falkenstein. Both providers do not meter traffic at these volumes, and they peer directly at DE-CIX Frankfurt with very large ports.
3. **Malicious mode (Profile A) recommendation:** Hetzner AX102 with the 10 Gbit/s uplink + OVHcloud VPS-6 in Strasbourg: about €275 a month at 5 and 20 TB, €280 at 50 TB. That is 27 %, 31 % and 39 % below the current plan. The OVHcloud side is a shared-core virtual machine with a 3 Gbit/s port that is not guaranteed; if it fails the tests, the runner-up is the OVHcloud Advance-3 dedicated server (3 Gbit/s guaranteed), at €372–377, which saves money only at 20 TB and above.
4. **Semi-honest mode (Profile B) recommendation:** the same Hetzner AX102 on its standard 1 Gbit/s unmetered port + OVHcloud VPS-5: €214 a month at every volume, 43 % below the current plan. Runner-up: Infomaniak (Geneva) + OVHcloud VPS-5, roughly €125, pending confirmation of Infomaniak's price and port speed.
5. **One pair serves both modes:** Hetzner dedicated + OVHcloud Strasbourg. Switching mode means adding or removing Hetzner's 10 Gbit/s uplink (€43 a month).
6. **The latency cost is real today.** At 6.5 ms, 11,500 sequential round trips take 75 s of network waiting alone, which is at or over a 60–90 s limit before any computation. The Hetzner + OVHcloud pair is comfortable only for the 2,800-round operation until the round counts come down. Helsinki + Tallinn gives 6 s and 24 s.
7. **Five database nodes** on five providers in five data-centre countries cost roughly €145–190 a month in total (section 6).

## Round-trip arithmetic

Network waiting only; computation and WireGuard processing come on top.

| Pair | Measured round trip | 2,800 rounds | 11,500 rounds |
|---|---|---|---|
| Helsinki (Hetzner) – Tallinn (WaveCom) | 2.1–2.2 ms | 5.9–6.2 s | 24–25 s |
| Zurich (Exoscale, cloudscale.ch) – Strasbourg (OVHcloud) | 3.2–4.1 ms | 9.0–11.5 s | 37–47 s |
| Nuremberg (Hetzner or netcup) – Strasbourg (OVHcloud) | 5.8–7.2 ms (one netcup probe 8.5) | 16–20 s | 67–83 s |
| Falkenstein (Hetzner) – Strasbourg (OVHcloud) | 7.8–8.8 ms | 22–25 s | 90–101 s |
| Rotterdam area (Worldstream) – Gravelines / Roubaix (OVHcloud) | 7.2–8.3 ms | 20–23 s | 83–95 s |
| Geneva (Infomaniak) – Strasbourg (OVHcloud) | 7.5 ms out, 11.3 ms back to a different Infomaniak host | 21–32 s | 86–130 s |
| Geneva (Infomaniak) – Nuremberg (Hetzner) | 11.5–12.7 ms | 32–36 s | 132–146 s |
| Stockholm (GleSYS, Bahnhof, UpCloud) – Helsinki (Hetzner) | 6.5–8.0 ms | 18–22 s | 75–92 s |

## 1. Traffic profiles and counting

**Profile A, malicious mode.** About 1.5 GB per unit of work, symmetric. Volume cases 5, 20 and 50 TB exchanged a month. Counting assumption: 1 TB exchanged means 0.5 TB sent by each node, so each node sends and receives 2.5, 10 and 25 TB. About 6 Gbit/s each way avoids being network-bound; 2.5 Gbit/s is a reasonable middle; 1 Gbit/s costs about a factor of six.

**Profile B, semi-honest mode.** The garbler sends 0.5, 2 or 5 TB a month; the other node sends almost nothing and receives the same volume. I treat the extra symmetric gigabyte in a quarter of sessions as included in those figures. About 2 Gbit/s out of the garbler is ideal; 1 Gbit/s costs about a factor of two.

How each provider counts:

| Provider and product | Port | Included | What counts | Beyond the allowance | Source |
|---|---|---|---|---|---|
| Hetzner dedicated, standard port | 1 Gbit/s | unlimited | nothing | "All root servers have a dedicated 1 GBit uplink by default and with it unlimited traffic." "There is no bandwidth limitation." No guarantee wording | https://docs.hetzner.com/robot/general/traffic/ (fetched) |
| Hetzner dedicated, 10G uplink (€43/month; auction servers are eligible by support ticket) | 10 Gbit/s | 20 TB | outbound only: "Incoming and internal traffic is unlimited." | €1.00/TB | https://docs.hetzner.com/robot/dedicated-server/network/10g-uplink/ and https://docs.hetzner.com/robot/general/pricing/price-list-for-additional-products (fetched) |
| Hetzner cloud (CCX) | shared 10 Gbit/s host link; "you can expect about 300-500 Mbits" | 20–60 TB | outbound | €1.00/TB | https://www.hetzner.com/cloud/general-purpose/ (fetched) |
| OVHcloud Advance dedicated | 3 Gbit/s "unmetered and guaranteed"; 4 Gbit/s +€200, 5 Gbit/s +€250 | unlimited | nothing | "Your public bandwidth is unlimited and unmetered"; but if limits are exceeded "your service may continue running but with reduced connection quality or throttled load" | catalogue; https://www.ovhcloud.com/en-ie/bare-metal/bandwidth/ (fetched) |
| OVHcloud VPS (2026 range) | VPS-4 2 Gbit/s, VPS-5 2.5 Gbit/s, VPS-6 3 Gbit/s; not guaranteed | "Unlimited traffic" in Europe | nothing | No fair-use text on the product page. Asia-Pacific sites have quotas with a 10 Mbit/s cap; Europe does not. A 2015 VPS contract allowed throttling to 1 Mbit/s for "excessive use"; I could not read the current contract | catalogue; https://www.ovhcloud.com/en-gb/vps/unmetered-vps/ (fetched) |
| WaveCom dedicated | 10 Gbit/s | 10 TB | in + out (owner's information; the page states no traffic terms) | €2/TB committed, €2.50/TB overage (owner's information) | https://www.wavecom.ee/en/dedicated-server (fetched; no traffic terms shown) |
| netcup root server and VPS | "up to 2.5 Gbit/s" | flat rate | unknown | Not on the overview pages. A netcup G11 root-server page says: above 3 TB in the last 24 hours, "a temporary throttling to 300 MBit/s takes place". A G12 VPS page: 200 Mbit/s when the 24-hour average exceeds 2 TB. Both from search snippets; the G12.5 product pages returned 404 | https://www.netcup.com/en/server/root-server (fetched), snippets of netcup.com product pages |
| Worldstream dedicated | "1Gbit/s Guaranteed" (10 Gbit/s on models from €399) | "100 TB traffic per month" | not stated | not stated | https://www.worldstream.com/en/dedicated-servers (fetched) |
| Infomaniak public cloud | not published; a third-party test of a small flavour measured 0.9–1.3 Gbit/s | "bandwidth is free" | nothing | none stated | https://www.infomaniak.com/en/hosting/public-cloud/prices (wording from `PROVIDERS.md` and a search snippet today) |
| UpCloud | not checked | 13–25 TB on 64 GB plans | outbound only | "we may throttle the bandwidth on the cloud services down to 100 Mbit/s" | https://upcloud.com/docs/products/networking/network-transfer/ (fetched) |
| Exoscale | not published | 1.42 GiB per hour per instance, about 1 TB a month | outbound only | about $0.02/GB (third-party figure) | https://www.exoscale.com/pricing/ (fetched; prices did not render) |
| cloudscale.ch | not published | 100 GB per 24 hours per server | not stated | CHF 2 per 100 GB | https://www.cloudscale.ch/en/pricing (fetched) |

## 2. Products considered

All prices per month, excluding VAT.

| Provider | Product | CPU and cores | RAM, storage | Kind | Price | Setup, term | Source |
|---|---|---|---|---|---|---|---|
| Hetzner | AX102 | Ryzen 9 7950X3D, 16 cores | 128 GB DDR5 ECC, 2 NVMe | dedicated | from €159 | €129 setup; monthly | https://www.hetzner.com/dedicated-rootserver/matrix-ax/ (fetched) |
| Hetzner | AX42 (step-down) | Ryzen 7 PRO 8700GE, 8 cores | 64 GB DDR5 | dedicated | €79–99 | €49 setup | same page |
| Hetzner | Server auction | varies (Ryzen 9 3900 / 5950X, Core i9) | varies | dedicated, used | "from €75.70" for the cheapest machine of any kind; a 12-core, 64 GB machine is probably €85–110. Not verified: the list could not be read. An April 2026 analysis reports shrinking stock and an average price of €98 | no setup fee; 1 Gbit/s, unlimited traffic | https://www.hetzner.com/sb/ (fetched); https://blog.iodev.org/blog/hetzner-auction-supply-crunch/ (via a reader mirror) |
| Hetzner | CCX43 cloud | AMD, model not stated, 16 dedicated vCPU | 64 GB, 360 GB | virtual, dedicated vCPU | €234.99 Helsinki, €276.49 Germany; €0.3766/hour | hourly | https://www.hetzner.com/cloud/general-purpose/ (fetched) |
| OVHcloud | Advance-3 | EPYC 4464P, 12 cores / 24 threads | 64 GB DDR5 ECC, 2x960 GB NVMe | dedicated | €170 (catalogue). The public web page shows Advance-1 and Advance-2 at €114.99 and €154.99 where the catalogue has €89.99 and €125, so the order form may show up to about €215 for Advance-3. Confirm before ordering | installation fee equal to one month, waived with a 12- or 24-month commitment | catalogue; https://www.ovhcloud.com/en-ie/bare-metal/advance/ (fetched) |
| OVHcloud | Advance-2 (step-down) | EPYC 4344P, 8 cores | 64 GB | dedicated | €125 catalogue, €154.99 web page | as above | same |
| OVHcloud | VPS-6 (2026 range) | model not stated, 24 vCores | 96 GB, 400 GB NVMe | virtual, shared cores | €72.99 (catalogue) | none; monthly | catalogue |
| OVHcloud | VPS-5 (2026 range) | model not stated, 16 vCores | 64 GB, 350 GB NVMe | virtual, shared cores | €54.99 (catalogue) | none; monthly | catalogue |
| OVHcloud | VPS-4 (2026 range; step-down) | 12 vCores | 48 GB, 300 GB | virtual, shared cores | €36.99 (catalogue) | none | catalogue |
| OVHcloud | b3-64 public cloud | 16 vCores at 2.3 GHz, model not stated | 64 GB, 400 GB NVMe | virtual | €0.4092/hour, about €299/month; 4 Gbit/s not guaranteed | hourly | catalogue |
| WaveCom | HPE BL460 G10 Premium Instant | Xeon Gold 6242, 16 cores | 64 GB, 800 GB SSD | dedicated | €175 | not stated | https://www.wavecom.ee/en/dedicated-server (fetched) |
| WaveCom | HPE BL460 G10 Instant (step-down) | Xeon Gold 6226, 12 cores | 32 GB | dedicated | €125 | not stated | same |
| netcup | RS 8000 G12.5 | EPYC 9645, 16 dedicated cores | 64 GB, 1 TB NVMe | virtual, dedicated cores | €148.42 on a 12-month contract; about 13 % more month to month | 30-day money-back | https://www.netcup.com/en/server/root-server (fetched) |
| netcup | VPS 8000 G12.5 | x86, 16 shared vCores | 64 GB, 1 TB | virtual, shared cores | €67.11 on a 12-month contract | as above | https://www.netcup.com/en/server/vps (fetched) |
| netcup | RS 4000 / VPS 4000 (step-down) | 12 cores | 32 GB | virtual | €77.83 / €45.36 | as above | same pages |
| Infomaniak | a16-ram64 public cloud | AMD EPYC (Rome generation), 16 vCPU | 64 GB; disk billed separately | virtual; dedicated or shared not stated | €0.081/hour, about €59/month plus storage. Third-party listing only | hourly | https://pcr.cloud-mercato.com/providers/infomaniak/flavors/a16-ram64-disk0 (fetched) |
| Worldstream | Dell R6515 | EPYC 7402P, 24 cores | 64 GB | dedicated | from €120 | no setup fee | https://www.worldstream.com/en/dedicated-servers (fetched) |
| Worldstream | ASRock 1U2S-B650 | Ryzen 9 9900X, 12 cores | 64 GB | dedicated | from €159 | no setup fee | same |
| GleSYS | X11-1 | Xeon Gold 6132, 14 cores | 64 GB, 2x480 GB SSD | dedicated, 10 Gbit/s port | €265, 36-month commitment | | https://glesys.com/pricing (fetched) |
| Exoscale | Standard Mega | 12 cores | 64 GB | virtual | about €0.657/hour in Geneva and Frankfurt, about €473/month (third-party) | hourly | https://pcr.cloud-mercato.com/providers/exoscale/flavors/mega-standard (search snippet) |
| cloudscale.ch | Flex-64-16 | 16 vCPU | 64 GB | virtual | CHF 17.60 per day, about CHF 528/month | daily | https://www.cloudscale.ch/en/pricing (fetched) |

All the CPUs named have AES-NI. The Ryzen 9 7950X3D, EPYC 4464P and EPYC 9645 also have SHA extensions and VAES; the Xeon Gold 6242 and 6226 (Cascade Lake) and the EPYC 7402P have AES-NI, and the EPYC has SHA extensions while the Cascade Lake Xeons do not. The OVHcloud VPS and Infomaniak CPU models are not published; check `/proc/cpuinfo` on a test instance.

Considered and set aside:

- **Scaleway (France; Iliad group).** Elastic Metal prices from a search snippet of Scaleway's page: EM-I120E, 8 cores, €134.99 from June 2026; EM-B220E, EPYC 7232P 8 cores, 64 GB, €119.99. Whether public traffic is unmetered is still unconfirmed. Its paths to Hetzner are poor: Paris–Falkenstein 16.4–20.9 ms and Amsterdam–Falkenstein 29–37 ms measured today. Its good paths are to other providers in the same country, which the jurisdiction rule excludes.
- **Contabo (Germany).** Owned by a US private-equity firm, and its Nuremberg network took 9.3 ms to Hetzner in the same city in the earlier study. Excluded on ownership.
- **Leaseweb (Netherlands).** Prices not fetchable; the earlier snippet showed €183 for 100 TB on 1 Gbit/s. No advantage over Worldstream.
- **UpCloud (Finland).** Throttles to 100 Mbit/s beyond 13–25 TB of outbound traffic on 64 GB plans; prices not fetchable. Usable only as a Profile B receiver or a database node.
- **Exoscale and cloudscale.ch (Zurich).** The best cross-border path found after Helsinki–Tallinn (3.2–4.1 ms to OVHcloud Strasbourg), but the Zurich node alone costs about €470–530 a month.
- **GleSYS, Bahnhof (Sweden).** Stockholm–Helsinki measured 7.6–8.0 ms; GleSYS's 10 Gbit/s server is €265 on a 36-month term. Bahnhof prices not researched.
- **1984, FlokiNET (Iceland).** 67 ms from Reykjavik to Helsinki. Database nodes only, and 1984's 16 GB plan is €139.52.
- **Cherry Servers (Lithuania).** 39.6 ms from Šiauliai to Hetzner Helsinki; pricing page did not render.
- **OVHcloud Warsaw.** 18.1 ms to Hetzner Helsinki and 23.7 ms to Falkenstein.
- **M247 and other Romanian or Czech hosts.** Not researched beyond the earlier finding of 10–12 ms from Hetzner to Prague. M247's ownership was not checked.
- **Hyperscale clouds and other US-headquartered companies.** Excluded by the jurisdiction rule.

## 3. Shortlisted pairs

Every pair has two different companies incorporated in different countries and data centres in different countries.

### Pair N — Helsinki + Tallinn: Hetzner + WaveCom (the current plan, and a lean variant)

- **Products.** Hetzner AX102 in HEL1, €159, with the 10G uplink at €43. WaveCom BL460 G10 Premium Instant, €175.
- **Lean variant.** Drop the 10G uplink (€334 before WaveCom traffic), or replace the AX102 with an auction server in HEL1 and keep the uplink (an estimated €130–155 for the Hetzner side; the auction price is not verified). WaveCom's €175 and its traffic terms are the part that does not come down.
- **Path.** 2.14–2.25 ms measured today (WaveCom Tallinn probe to Hetzner HEL1), matching 2.04–2.25 ms earlier in the evening. PeeringDB shows no exchange in common: WaveCom lists only RTIX with 80 Gbit/s in total; Hetzner lists FICIX and PITER-IX Helsinki. The short path therefore runs over a private link or a transit provider that I could not identify, and its capacity is unknown. Run `mtr` from a rented machine.
- **Throughput.** 10 Gbit/s ports at both ends. No public throughput data for the path.

### Pair S1 — Nuremberg or Falkenstein + Strasbourg: Hetzner + OVHcloud, both dedicated

- **Products.** Hetzner AX102 (€159) with the 10G uplink (€43). OVHcloud Advance-3 in Strasbourg (SBG), €170 by catalogue, 3 Gbit/s unmetered and guaranteed.
- **Path.** Hetzner Nuremberg to OVHcloud Strasbourg 6.23–6.39 ms and 6.32 ms (three probes); OVHcloud Strasbourg to Hetzner Nuremberg 7.14–7.18 ms (two runs). Falkenstein to Strasbourg 7.81–7.83 ms; back 8.71 ms. Hetzner lists its dedicated AX servers mainly in Falkenstein and Helsinki; if NBG1 has no stock, plan on the Falkenstein figures.
- **Peering.** Both networks have open peering policies and meet at DE-CIX Frankfurt (Hetzner 2,800 Gbit/s of ports, OVHcloud 1,600 Gbit/s), AMS-IX, France-IX Paris, NL-ix and about twenty other exchanges (PeeringDB `netixlan`, fetched today). A direct peering at Frankfurt is consistent with the measured times. Exchange capacity is not a guarantee for one flow.
- **Throughput.** Bounded by OVHcloud's 3 Gbit/s; 5 Gbit/s costs €250 more. Both providers publish 10 GB test files (`https://nbg1-speed.hetzner.com/10GB.bin`, `https://sbg.proof.ovh.net/files/10Gb.dat`; headers read today, both 10,737,418,240 bytes). I did not download them.

### Pair S2 — the same two providers, OVHcloud side virtual

- **Products.** Hetzner AX102, with the 10G uplink for Profile A and without it for Profile B. OVHcloud VPS-6 (24 vCores, 96 GB, 3 Gbit/s, €72.99) for Profile A, or VPS-5 (16 vCores, 64 GB, 2.5 Gbit/s, €54.99) for Profile B.
- **Path.** As S1, provided the VPS is ordered in Strasbourg. OVHcloud sells VPS in several European sites; confirm Strasbourg in the order form.
- **Throughput.** The VPS port speed is a ceiling, not a guarantee, and the cores are shared. This is the main thing to test.

### Pair S3 — Nuremberg + Strasbourg, both virtual: netcup + OVHcloud

- **Products.** netcup RS 8000 G12.5 (16 dedicated cores, €148.42) or VPS 8000 G12.5 (16 shared cores, €67.11), Nuremberg. OVHcloud VPS-5, Strasbourg.
- **Path.** netcup Nuremberg to OVHcloud Strasbourg 5.83–6.15 ms (three probes in one run), 5.97 ms and 8.53 ms (two probes in an earlier run). netcup has no rows at any exchange in PeeringDB and states its peering policy as "No"; its traffic goes through its parent Anexia and transit.
- **Throughput.** 2.5 Gbit/s nominal at both ends. netcup's daily-volume throttle (section 1) applies if it is still in force: 3 TB in 24 hours is 280 Mbit/s averaged over a day, which a busy day in Profile A exceeds.
- **Independence.** netcup's Nuremberg presence is inside a Hetzner building. That matters only if Hetzner also hosts something.

### Pair G — Geneva + Strasbourg: Infomaniak + OVHcloud

- **Products.** Infomaniak a16-ram64 (about €59 plus block storage, third-party figure) in Geneva. OVHcloud VPS-5 or Advance-3 in Strasbourg.
- **Path.** Infomaniak Geneva to OVHcloud Strasbourg 7.43–7.48 ms (two probes). OVHcloud Strasbourg to `www.infomaniak.com` 11.3 ms; that host may not be in the cloud data centre. Infomaniak and OVHcloud both peer at SwissIX.
- **Throughput.** Infomaniak publishes no port speed. The only figure is a third-party test of a small flavour at 0.9–1.3 Gbit/s. Treat as 1 Gbit/s until measured.
- **Variant.** Infomaniak + Hetzner Nuremberg: 11.5–12.0 ms out, 11.9 ms back.

### Pair W — Netherlands + northern France: Worldstream + OVHcloud

- **Products.** Worldstream Dell R6515, EPYC 7402P 24 cores, 64 GB, €120, 1 Gbit/s guaranteed, 100 TB. OVHcloud VPS-5 or Advance-3 in Gravelines or Roubaix.
- **Path.** Worldstream to OVHcloud Roubaix 8.02 ms and Gravelines 7.85 ms; OVHcloud Gravelines and Roubaix to Worldstream 7.56 ms and 7.21 ms. They share AMS-IX, NL-ix, DE-CIX Frankfurt and five other exchanges.
- **Throughput.** 1 Gbit/s on the Worldstream side.

## 4. Monthly cost of each pair

Profile A, both nodes plus traffic, at 5 / 20 / 50 TB exchanged:

| Pair | Configuration | 5 TB | 20 TB | 50 TB | Slower port | Arithmetic at 50 TB |
|---|---|---|---|---|---|---|
| N (current) | AX102 + 10G; WaveCom Premium | €377 | €397 | €462 | 10 Gbit/s | 159 + 43 + 5 (25 TB out, 5 over) + 175 + 80 (50 TB in + out, 40 over at €2); €482 at the €2.50 overage rate |
| N lean | AX102 on 1 Gbit/s; WaveCom Premium | €334 | €354 | €414 | 1 Gbit/s | 159 + 175 + 80 |
| S1 | AX102 + 10G; Advance-3 | €372 | €372 | €377 | 3 Gbit/s guaranteed | 159 + 43 + 5 + 170. Add about €45 if the web list price applies to Advance-3 |
| S2 | AX102 + 10G; VPS-6 | €275 | €275 | €280 | 3 Gbit/s, not guaranteed | 159 + 43 + 5 + 72.99 |
| S2 with VPS-5 | AX102 + 10G; VPS-5 | €257 | €257 | €262 | 2.5 Gbit/s, not guaranteed | 159 + 43 + 5 + 54.99 |
| S3 dedicated cores | netcup RS 8000; VPS-5 | €203 | €203 | €203 | 2.5 Gbit/s nominal, daily throttle | 148.42 + 54.99 |
| S3 shared cores | netcup VPS 8000; VPS-5 | €122 | €122 | €122 | 2.5 Gbit/s nominal, daily throttle | 67.11 + 54.99 |
| G | Infomaniak a16-ram64; VPS-5 | about €125 | about €125 | about €125 | about 1 Gbit/s, unknown | 59 + storage + 54.99; Infomaniak figures unverified |
| W | Worldstream R6515; VPS-5 | €175 | €175 | €175 | 1 Gbit/s guaranteed | 120 + 54.99 |

Profile B, at 0.5 / 2 / 5 TB sent by the garbler. Every pair is flat across these volumes, because the largest case is below every allowance:

| Pair | Configuration | Per month | Where to put the garbler | Garbler's outbound port |
|---|---|---|---|---|
| N (current) | AX102 + 10G; WaveCom Premium | €377 | Either. WaveCom counts inbound too, but 5 TB is inside its 10 TB | 10 Gbit/s |
| N lean | AX102 on 1 Gbit/s; WaveCom Premium | €334 | WaveCom, so the 1 Gbit/s Hetzner port is on the receiving side; or Hetzner, at 1 Gbit/s | 1–10 Gbit/s |
| S1 without the 10G uplink | AX102; Advance-3 | €329 | OVHcloud | 3 Gbit/s out, 1 Gbit/s in at Hetzner |
| S2 | AX102 on 1 Gbit/s; VPS-5 | €214 | Either; both ends are unmetered. The Hetzner port limits the flow to 1 Gbit/s; add the 10G uplink (€257 in total) for 2 Gbit/s | 1 Gbit/s |
| S3 dedicated cores | netcup RS 8000; VPS-5 | €203 | OVHcloud, since netcup's throttle rule may count either direction | 2.5 Gbit/s nominal |
| S3 shared cores | netcup VPS 8000; VPS-5 | €122 | OVHcloud | 2.5 Gbit/s nominal |
| G | Infomaniak a16-ram64; VPS-5 | about €125 | OVHcloud | 2.5 Gbit/s nominal out, about 1 Gbit/s in |
| W | Worldstream R6515; VPS-5 | €175 | OVHcloud | 1 Gbit/s at Worldstream |

Step down to 8 cores and 32 GB or the nearest plan, for Profile B if the workload allows: Hetzner AX42 (8 cores, 64 GB) at €79–99 with OVHcloud VPS-4 (12 vCores, 48 GB, 2 Gbit/s) at €36.99 gives €116–136 a month. Other step-downs: OVHcloud Advance-2 €125–155, netcup RS 4000 €77.83, WaveCom BL460 G10 Instant €125.

## 5. Rankings and recommendation

### Profile A (malicious mode)

| Rank | Jurisdiction first | Cost first (20 TB) | Throughput first |
|---|---|---|---|
| 1 | N: Finland + Estonia | S3 shared cores, €122 | N: 10 Gbit/s both ends |
| 2 | G: Switzerland + France | G, about €125 | S1: 10 Gbit/s and 3 Gbit/s guaranteed |
| 3 | S1, S2: Germany + France, dedicated on at least one side | W, €175 | S2: 10 Gbit/s and 3 Gbit/s shared |
| 4 | S3: Germany + France, both virtual | S3 dedicated cores, €203 | S3: 2.5 Gbit/s both, with a daily throttle |
| 5 | W: Netherlands + France | S2, €257–275 | G: about 1 Gbit/s |
| 6 | | S1, €372 | W and N lean: 1 Gbit/s |
| 7 | | N lean €354; N €397 | |

**Recommended: S2, Hetzner AX102 with the 10G uplink + OVHcloud VPS-6 in Strasbourg, €275 / €275 / €280.**
**Runner-up: S1, the same Hetzner server + OVHcloud Advance-3, €372 / €372 / €377.**

Reasons. Hetzner + OVHcloud is the only cheaper combination with direct, very large peering between the two networks, no traffic metering on either side at these volumes, and a port above 2.5 Gbit/s at both ends. S2 costs about €100 less than the current plan at 5 TB and about €180 less at 50 TB. Its weak point is the virtual machine: shared cores under a sustained 12-core load and a port speed that is a ceiling. S1 removes both doubts with a dedicated EPYC 4464P and a guaranteed 3 Gbit/s, but then the saving is €5 at 5 TB, €25 at 20 TB and €85 at 50 TB, and nothing at all if OVHcloud's higher web price applies.

Against the current Helsinki + Tallinn plan:

| Criterion | Current plan | S2 | S1 |
|---|---|---|---|
| Jurisdiction | Finland and Estonia, both outside the Five, Nine and Fourteen Eyes lists; German and Estonian companies | Germany and France, both inside those lists and close partners; German and French companies. Worse | Same as S2 |
| Throughput | 10 Gbit/s ports both ends; path capacity unknown, no common exchange | 10 Gbit/s and 3 Gbit/s shared; direct peering at DE-CIX. Lower ceiling, better-evidenced path | 10 Gbit/s and 3 Gbit/s guaranteed |
| Cost at 5 / 20 / 50 TB | €377 / €397 / €462 | €275 / €275 / €280 | €372 / €372 / €377 |
| Round trip | 2.1 ms: 6 s and 24 s | 6.2–7.2 ms from Nuremberg: 17–20 s and 71–83 s | Same as S2 |

If jurisdiction strictly outranks cost, stay with Helsinki + Tallinn and trim it: an auction server in HEL1 with the 10G uplink in place of the new AX102 saves an estimated €45–70 a month.

### Profile B (semi-honest mode)

| Rank | Jurisdiction first | Cost first | Throughput first (garbler's outbound) |
|---|---|---|---|
| 1 | N lean: Finland + Estonia, €334 | S3 shared cores, €122 | N: 10 Gbit/s |
| 2 | G: Switzerland + France | G, about €125 | S1, S2 with the 10G uplink: 2.5–3 Gbit/s |
| 3 | S2: Germany + France, one side dedicated | W, €175 | S3: 2.5 Gbit/s nominal |
| 4 | S3 | S3 dedicated cores, €203 | S2 on 1 Gbit/s, W, G: about 1 Gbit/s |
| 5 | W | S2, €214 | |

**Recommended: S2, Hetzner AX102 on the standard 1 Gbit/s port + OVHcloud VPS-5 in Strasbourg, €214 at every volume.**
**Runner-up: G, Infomaniak a16-ram64 in Geneva + OVHcloud VPS-5, about €125**, once Infomaniak's price, port speed and core type are confirmed. It puts one node in Switzerland, which is outside the EU and the Eyes groupings.

Reasons. Profile B needs 1–2 Gbit/s one way and at most 5 TB a month, which every candidate carries without charge, so the choice turns on jurisdiction and on how much to trust shared cores. S2 keeps one node on bare metal with 16 dedicated cores and uses the same two providers as the Profile A recommendation. The all-virtual pair S3 is €92 cheaper, but both nodes are then exposed to the host operator and to noisy neighbours.

Against the current plan: €214 instead of €377, a saving of €163 or 43 %. Jurisdiction is worse (Germany + France instead of Finland + Estonia). The garbler's link is 1 Gbit/s, about a factor of two slower than ideal; the 10G uplink restores it for €43. Round trip 6.2–7.2 ms instead of 2.1 ms.

### One pair for both modes

Hetzner dedicated + OVHcloud Strasbourg. Order the Hetzner server with the 10G uplink from the start (moving an existing server to a 10G rack costs €32.77–99 and changes its address) and choose VPS-6. That is €275 a month in either mode. Running Profile B only, the uplink and the larger VPS can be dropped for €214.

## 6. Database nodes

Requirement: 4 cores, 16 GB, little traffic, at least three and ideally five providers in different jurisdictions, none hosting three.

| # | Provider | Company; parent | Data centre | Product | Price per month | Source |
|---|---|---|---|---|---|---|
| 1 | OVHcloud | France; OVH Groupe SA | Gravelines or Roubaix, France | VPS-3 (2026 range): 8 vCores, 24 GB, 200 GB | €19.99 | catalogue |
| 2 | netcup | Germany; Anexia, Austria | Vienna, Austria | VPS 2000 G12.5: 8 vCores, 16 GB, 256 GB. RS 2000 with dedicated cores is €40.70 | €26.92 on a 12-month contract | https://www.netcup.com/en/server/vps (fetched) |
| 3 | Infomaniak | Switzerland; a press release found today says the founder has transferred control to a foundation (not read) | Geneva, Switzerland | a4-ram16 or a8-ram16 public cloud plus a disk | about €20–30; a third-party listing gives a8-ram16 at €0.040/hour. Unverified | search snippet of pcr.cloud-mercato.com |
| 4 | Hetzner | Germany; privately held | Helsinki, Finland | CX43: 8 shared vCPU, 16 GB, €16.49, but shown as "currently unavailable" today. Otherwise CPX42: 8 vCPU, 16 GB | €16.49, or €59.49 | https://www.hetzner.com/cloud/cost-optimized/ and https://www.hetzner.com/cloud/regular-performance/ (fetched) |
| 5 | WaveCom | Estonia | Tallinn, Estonia | KVM VPS built to order: €8 base + 4 vCPU at €3 + 16 GB at €2 + 80 GB at €0.10 | €60 | https://www.wavecom.ee/en/vps (fetched) |

Total: about €145 a month with Hetzner's CX43, about €190 with the CPX42.

**Sharing a provider with a computation node.** With the recommended computation pair, rows 1 and 4 are at OVHcloud and Hetzner. Three database nodes together can reconstruct what a computation node alone cannot. A provider that hosts one computation node and one database node therefore needs only two more database nodes, instead of three, to combine that reconstruction with a computation node's state; and the two computation providers together would already hold two of the three database shares needed. To avoid this, replace rows 1 and 4 with providers that host no computation node:

- **UpCloud** (Finland; Helsinki or Stockholm). 4-CPU, 16 GB plans exist with 2.5–7 TB of transfer; price not fetchable today.
- **Scaleway** (France; Paris, Amsterdam or Warsaw). Price not fetchable today.
- **Worldstream** (Netherlands) sells dedicated servers only; **Leaseweb** (Netherlands) price not fetchable.
- **1984** (Iceland): VPS #5, 6 vCPU, 16 GB, €139.52 (https://1984.hosting/product/pricelist/, fetched). **FlokiNET** (Iceland, Romania, Finland): no 16 GB VPS; the 12 GB plan is €73.90 (https://flokinet.is/vps, fetched).
- **GleSYS** (Sweden): 4 vCPU, 8 GB is €77.28; 16 GB costs more.

If WaveCom keeps a computation node, the same reasoning applies to row 5.

## 7. Jurisdiction, by candidate

"Nothing found" means my searches today returned nothing; it does not mean nothing exists. General-law statements are a summary of publicly known law, not legal advice.

| Provider | Operating company; ultimate parent | Data centre used here | Legal regimes that can reach it | Public record |
|---|---|---|---|---|
| Hetzner | Hetzner Online GmbH, Germany; privately held; subsidiaries in Finland and the United States | Germany (Nuremberg, Falkenstein) or Finland (Helsinki) | German criminal procedure and intelligence law for the company and the German sites; Finnish law for Helsinki; a US subsidiary exists, which is a possible lever for US orders | No transparency report or warrant canary found. In 2023 traffic to a customer's server in Germany was intercepted by rerouting inside the provider's network, probably lawful interception; Hetzner did not comment (https://therecord.media/jabber-ru-alleged-government-wiretap-expired-tls-certificate) |
| OVHcloud | OVH SAS; OVH Groupe SA, France, listed in Paris, controlled by the founding family; separate US and Canadian subsidiaries | France (Strasbourg, Gravelines, Roubaix) | French law, including the 2015 intelligence law; EU instruments; its US entity is kept legally separate | Publishes Digital Services Act transparency reports for 2024 and 2025 (https://corporate.ovhcloud.com/en/trusted-cloud/ethics-compliance/); I did not read the figures. Its US FAQ says it requires a valid court order and routes non-US requests through mutual legal assistance. In 2025 an Ontario court ordered it to produce data held in Europe through its Canadian subsidiary; OVHcloud is contesting it and cites the French blocking statute (https://www.theregister.com/2025/11/27/canada_court_ovh) |
| WaveCom | Aktsiaselts WaveCom, Estonia, registry code 10756058; shareholders not found | Tallinn, own data centre | Estonian law; EU instruments | Nothing found |
| netcup | netcup GmbH, Germany; Anexia, Austria | Nuremberg (inside a Hetzner building) or Vienna | German law; Austrian law for the parent and Vienna | Nothing found |
| Infomaniak | Infomaniak Network SA, Switzerland; a press-release headline found today says the founder has transferred control to a foundation (not read) | Geneva | Swiss surveillance law (BÜPF/LSCPT) and its ordinances, under revision; not subject to EU instruments | No transparency report found. In June 2025 it wrote that "Requests for data access should always require judicial approval" and that it opposes the ordinance revision in its current form, while also stating "we require a real identity upon registration" (https://news.infomaniak.com/en/viewpoint-lscpt/). A privacy forum reads its position as supportive of the revision; that is commentary, not a primary source |
| Worldstream | Worldstream B.V., Netherlands | Naaldwijk, Netherlands | Dutch law, including the 2017 intelligence act | Publishes Digital Services Act transparency reports for 2024 and 2025 (https://www.worldstream.com/media/uploads/2026/04/WS-Digital-Services-Act-transparency-report-2025.pdf); the file could not be read as text |
| UpCloud | UpCloud Oy, Finland | Finland, Sweden and others | Finnish law; local law per site | Its EU Data Act page, per a search snippet, says it rejects information requests from foreign authorities and refers them to Finnish authorities for mutual legal assistance. The page itself returned 403 |
| Exoscale | Akenes SA, Switzerland; A1 Telekom Austria group | Zurich, Geneva | Swiss law; Austrian parent | Nothing found |
| cloudscale.ch | cloudscale.ch AG, Switzerland | Zurich area | Swiss law | Not researched |
| Scaleway | Scaleway SAS, France; Iliad group | France, Netherlands, Poland | French law; local law per site | Nothing found |
| GleSYS, Bahnhof | Swedish companies | Sweden | Swedish law, including the signals-intelligence act covering cross-border cables | Not researched today |
| 1984, FlokiNET | Icelandic companies | Iceland | Icelandic law | Not researched today |

Country pairs, for the recommended and alternative pairs:

- **Finland + Estonia.** Both outside the Five, Nine and Fourteen Eyes lists; both EU and NATO members, so European investigation orders apply between them.
- **Switzerland + France.** Switzerland is outside the EU and the lists; France is in the Nine Eyes list and has a broad intelligence law.
- **Germany + France.** Both in the wider lists, with close police and intelligence cooperation. A single European investigation order process reaches both, though through two national authorities.
- **Netherlands + France.** Both in the Nine Eyes list.

Public information cannot show that any provider refuses informal requests. Two different states and two different facility operators is what the pairs above deliver; none delivers more than that.

## 8. What was not verified, and how to settle it

### Not verified

- Throughput on any path, and whether any provider throttles a long symmetric encrypted flow.
- OVHcloud VPS: the CPU model, how shared cores behave under a sustained 12-core load, whether Strasbourg is offered for VPS-5 and VPS-6, the current contract's fair-use clause, and whether VPS-5 and VPS-6 of the 2026 range are still orderable (the public page showed only VPS-1 to VPS-4 of a newer range before it was cut off).
- OVHcloud Advance-3's price in the order form (catalogue €170; web page prices for its smaller siblings are about 25 % above the catalogue).
- Hetzner: auction prices and stock; whether an AX102 can be had in Nuremberg; the price in Helsinki versus Germany.
- netcup: the traffic throttle on G12.5 products, and whether inbound counts.
- Infomaniak: price, disk price, port speed, whether cores are dedicated.
- WaveCom: traffic terms on its own page, contract term, setup fee, ownership.
- Worldstream: whether the 100 TB counts both directions.
- Prices at Scaleway, UpCloud, Leaseweb, Bahnhof.
- Latency at other times of day and to rented machines; reverse direction for Tallinn.
- Confidential-computing support at any shortlisted provider.

### Measurement plan

Stage 1, hourly instances, about €15 in total, one afternoon. It tests the networks, not the final machines.

| Rent | Where | Price | Purpose |
|---|---|---|---|
| OVHcloud b3-64 public cloud (16 vCores, 64 GB, 4 Gbit/s) | Strasbourg | €0.41/hour | OVHcloud's Strasbourg network and backbone |
| Hetzner CCX43 (16 dedicated vCPU, 64 GB) | Nuremberg, then Falkenstein | €0.38/hour | Hetzner's network; note Hetzner's own "300-500 Mbits" expectation for cloud, so a poor throughput result here does not condemn the dedicated product |
| Infomaniak a16-ram64 | Geneva | about €0.08/hour | Only if pair G is of interest |

Stage 2, the real products, one month, about €330 plus €129 setup: a Hetzner AX102 with the 10G uplink (€202; or an auction server, which has no setup fee), an OVHcloud VPS-6 (€72.99) and, to compare, a VPS-5 (€54.99) in Strasbourg. Add a netcup RS 8000 under its 30-day money-back guarantee if pair S3 is of interest. Rent the OVHcloud Advance-3 only if the VPS fails.

Run, in both directions, inside WireGuard (MTU 1420) and outside it:

1. `mtr -rwzc 300` to record the path and confirm it stays on the direct peering.
2. `ping -i 0.2 -c 3000` at about 03:00, 10:00, 15:00 and 21:00 local time on three days including a weekend day; record the median and the 99th percentile.
3. `iperf3 -t 1800` with one stream, then `iperf3 -P 8 -t 1800`, then both directions at once (`--bidir`), watching for a step down during the 30 minutes.
4. A volume day: 1 TB each way within 24 hours, then check the provider's traffic graph, the invoice preview and the mailbox for notices. On netcup, push past 3 TB in a day to find the throttle.
5. CPU: `openssl speed -evp aes-128-ctr` and `-evp sha256` on 12 parallel processes for 30 minutes on the virtual machines; record steal time from `vmstat 5`. Then the real workload, ten runs of each operation.
6. `grep -m1 "model name" /proc/cpuinfo` and the flags `aes`, `sha_ni`, `vaes` on each virtual machine.

Pass criteria:

- Profile A: at least 2 Gbit/s sustained each way simultaneously for 30 minutes inside WireGuard, with no step down. Profile B: at least 1 Gbit/s one way.
- No throttle, notice or charge after 1 TB each way in a day.
- 99th-percentile round trip within 1.5 times the median at every time of day; packet loss below 0.01 %.
- Median round trip at most 7.5 ms from Nuremberg or 9 ms from Falkenstein.
- On virtual machines: steal time below 2 % and throughput of the CPU test within 10 % of its first minute throughout the 30 minutes.
- The time-limited operation completes inside its limit in all ten runs.

## 9. Risks

- **"Unmetered" with a throttle.** OVHcloud's bandwidth page reserves "reduced connection quality or throttled load". netcup throttles by daily volume. UpCloud throttles to 100 Mbit/s. Hetzner's 1 Gbit/s port has no stated limit and no stated guarantee. 25 TB sent in a month is an average of 77 Mbit/s, small against any of these ports; the exposure is in bursts and in daily-volume rules.
- **Shared cores.** OVHcloud VPS, netcup VPS and probably Infomaniak instances share physical cores. A sustained 12-core cryptographic load is the pattern providers throttle or complain about; netcup has had public disputes over throttling of cores sold as dedicated (reported by LowEndBox; not read today). Dedicated-core or bare-metal alternatives: Hetzner AX and CCX, OVHcloud Advance, netcup RS, Worldstream, WaveCom.
- **Suspension for traffic pattern.** A long, high-volume encrypted flow between two fixed addresses resembles a tunnel or a relay. I did not read each provider's acceptable-use terms. Tell support in advance, and keep the WireGuard port fixed and documented.
- **Virtual machines are readable by the host.** The provider's hypervisor can read a virtual machine's memory and disks without leaving a trace in the guest. In S2 one node has that weakness; in S3 and G both do. None of the shortlisted virtual products advertises AMD SEV-SNP or Intel TDX. IONOS (Germany) documents SEV-SNP confidential virtual machines in its EU data centres (https://docs.ionos.com/cloud/compute-services/compute-engine/confidential-computing-vm/overview); it was not priced or measured here. Bare metal avoids the hypervisor but not physical access or the management controller.
- **Contract terms and one-off fees.** Hetzner AX102 setup €129, AX42 €49, auction none. OVHcloud Advance: one month's fee for installation unless committed for 12 or 24 months. netcup's quoted prices are for 12-month contracts. GleSYS dedicated servers need 36 months. Moving a Hetzner server to a 10G rack later costs €32.77–99 and changes its address.
- **Prices move.** Hetzner raised dedicated prices by a reported 30–40 % on 1 April 2026 and cloud prices in June 2026; OVHcloud's catalogue and web page disagree today; Scaleway raised prices on 1 June 2026.
- **VAT.** All figures exclude VAT. An EU business customer with a valid VAT number is normally invoiced under reverse charge; otherwise the provider adds VAT at the customer's national rate (19–25.5 % in the EU). Infomaniak invoices from Switzerland under Swiss rules.
- **Account checks.** Hetzner, netcup and OVHcloud may ask for identity documents and can cancel new accounts during verification. Open accounts a week ahead.
- **Latency headroom.** The recommended pair leaves no margin for the 11,500-round operation at today's round count (section "Round-trip arithmetic").

## Scratch files to remove

The research left helper files in this directory; none is needed afterwards: `_scratch_gp.py`, `_scratch_ovh.py`, `_scratch_jobs1.txt`, `_scratch_jobs2.txt`, `_scratch_jobs3.txt`, `_scratch_jobs4.txt`, `_scratch_results.txt`. Four catalogue downloads made before the working rules were tightened sit in the session's temporary folder outside the repository.

## Appendix A — Raw measurements

Globalping public probes, 11 Nov 2026, 23:00–23:10 UTC, ICMP, 8 packets. Fields: label, probe network and city, target and address, minimum / average / maximum in ms, loss in percent, measurement ID (retrievable for a limited time at `https://api.globalping.io/v1/measurements/<id>`). Targets `www.infomaniak.com` and `www.cloudscale.ch` are company web hosts and may not sit beside the cloud servers. `waw.proof.ovh.net` and `fra.proof.ovh.net` did not resolve, and no netcup probe exists in Amsterdam, so those rows are omitted.

```
HetznerFSN->OVH SBG | src Hetzner Online AS24940 Falkenstein,DE -> sbg.proof.ovh.net (51.91.75.40) | min 7.811 avg 7.918 max 8.053 loss 0 | id 2qw3IlnKtaMSLbXtI00021UFj
HetznerFSN->OVH SBG | src Hetzner Online AS24940 Falkenstein,DE -> sbg.proof.ovh.net (51.91.75.40) | min 7.83 avg 7.888 max 7.987 loss 0 | id 2qw3IlnKtaMSLbXtI00021UFj
HetznerNBG->OVH SBG | src Hetzner Online AS24940 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 6.229 avg 6.388 max 6.944 loss 0 | id 2mATBLwL97zMP5EKW00021UFj
HetznerNBG->OVH SBG | src Hetzner Online AS24940 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 6.253 avg 6.363 max 6.554 loss 0 | id 2mATBLwL97zMP5EKW00021UFj
HetznerNBG->OVH SBG (repeat) | src Hetzner Online AS24940 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 6.322 avg 6.548 max 7.345 loss 0 | id 2VZCz4vHzL7kWhBwB00021UFv
HetznerFSN->OVH GRA | src Hetzner Online AS24940 Falkenstein,DE -> gra.proof.ovh.net (141.94.30.145) | min 13.472 avg 13.586 max 13.711 loss 0 | id 2BTVWhfVCf7EHDdym00021UFj
HetznerFSN->OVH RBX | src Hetzner Online AS24940 Falkenstein,DE -> rbx.proof.ovh.net (141.95.207.211) | min 12.759 avg 12.856 max 13.024 loss 0 | id 23EsuPcKfJDFFCeIh00021UFj
OVH SBG->Hetzner FSN | src OVH AS16276 Strasbourg,FR -> fsn1-speed.hetzner.com (78.46.170.2) | min 8.711 avg 8.771 max 8.854 loss 0 | id 2uS1qo3ltCq4FLdVE00021UFj
OVH SBG->Hetzner NBG | src OVH AS16276 Strasbourg,FR -> nbg1-speed.hetzner.com (78.47.119.196) | min 7.176 avg 7.207 max 7.284 loss 0 | id 2LsSInTAvI6Hn8RsC00021UFj
OVH SBG->Hetzner NBG (repeat) | src OVH AS16276 Strasbourg,FR -> nbg1-speed.hetzner.com (78.47.119.196) | min 7.141 avg 7.189 max 7.275 loss 0 | id 2V61NZ1HAx5s3J6dL00021UFv
OVH GRA->Hetzner FSN | src OVH AS16276 Gravelines,FR -> fsn1-speed.hetzner.com (78.46.170.2) | min 13.382 avg 13.43 max 13.517 loss 0 | id 2Ome6hfJgCCDigUdU00021UFj
OVH RBX->Hetzner FSN | src OVH AS16276 Roubaix,FR -> fsn1-speed.hetzner.com (78.46.170.2) | min 12.799 avg 12.975 max 13.186 loss 0 | id 2Y29JqHC4LgxNzXO100021UFj
OVH WAW->Hetzner FSN | src OVH AS16276 Warsaw,PL -> fsn1-speed.hetzner.com (78.46.170.2) | min 23.662 avg 25.128 max 35.161 loss 0 | id 2gfK0U2VD9IQT92PQ00021UFj
OVH WAW->Hetzner HEL | src OVH AS16276 Warsaw,PL -> hel1-speed.hetzner.com (95.217.255.81) | min 18.139 avg 18.214 max 18.307 loss 0 | id 21vKGInbyYOsTby8100021UFj
netcupNUE->OVH SBG | src netcup AS197540 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 8.529 avg 8.597 max 8.669 loss 0 | id 2xglQvVKqYSUGpm4A00021UFj
netcupNUE->OVH SBG | src netcup AS197540 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 5.973 avg 5.998 max 6.022 loss 0 | id 2xglQvVKqYSUGpm4A00021UFj
netcupNUE->OVH SBG (repeat) | src netcup AS197540 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 5.829 avg 5.894 max 5.951 loss 0 | id 2tda6cxJZLYl39nAm00021UFv
netcupNUE->OVH SBG (repeat) | src netcup AS197540 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 6.147 avg 6.304 max 6.783 loss 0 | id 2tda6cxJZLYl39nAm00021UFv
netcupNUE->OVH SBG (repeat) | src netcup AS197540 Nuremberg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 6.075 avg 6.112 max 6.16 loss 0 | id 2tda6cxJZLYl39nAm00021UFv
netcupVIE->OVH SBG | src netcup AS197540 Vienna,AT -> sbg.proof.ovh.net (51.91.75.40) | min 17.346 avg 17.388 max 17.438 loss 0 | id 2jdnxPbbDfobpLVLG00021UFj
netcupVIE->OVH SBG | src netcup AS197540 Vienna,AT -> sbg.proof.ovh.net (51.91.75.40) | min 23.45 avg 23.479 max 23.508 loss 0 | id 2jdnxPbbDfobpLVLG00021UFj
netcupVIE->Hetzner NBG | src netcup AS197540 Vienna,AT -> nbg1-speed.hetzner.com (78.47.119.196) | min 8.796 avg 8.854 max 8.993 loss 0 | id 2NpZ2IrvAsoxdkuto00021UFj
ScalewayPAR->Hetzner FSN | src SCALEWAY AS12876 Paris,FR -> fsn1-speed.hetzner.com (78.46.170.2) | min 16.411 avg 16.478 max 16.6 loss 0 | id 2NTujz7hCddP5iTDG00021UFj
ScalewayPAR->Hetzner FSN | src SCALEWAY AS12876 Paris,FR -> fsn1-speed.hetzner.com (78.46.170.2) | min 20.642 avg 20.864 max 21.175 loss 0 | id 2NTujz7hCddP5iTDG00021UFj
ScalewayAMS->Hetzner FSN | src SCALEWAY AS12876 Amsterdam,NL -> fsn1-speed.hetzner.com (78.46.170.2) | min 35.282 avg 35.426 max 35.595 loss 0 | id 205S3uPdUEdZWIQWG00021UFj
ScalewayAMS->Hetzner FSN | src SCALEWAY AS12876 Amsterdam,NL -> fsn1-speed.hetzner.com (78.46.170.2) | min 37.001 avg 37.183 max 37.413 loss 0 | id 205S3uPdUEdZWIQWG00021UFj
ScalewayAMS->Hetzner NBG | src SCALEWAY AS12876 Amsterdam,NL -> nbg1-speed.hetzner.com (78.47.119.196) | min 31.805 avg 32.004 max 32.458 loss 0 | id 29RMNHGhPK0iJE7BM00021UFj
ScalewayWAW->Hetzner FSN | src SCALEWAY AS12876 Warsaw,PL -> fsn1-speed.hetzner.com (78.46.170.2) | min 18.046 avg 18.126 max 18.185 loss 0 | id 2FA955lmtbOFRbCkf00021UFj
ScalewayWAW->Hetzner HEL | src SCALEWAY AS12876 Warsaw,PL -> hel1-speed.hetzner.com (95.217.255.81) | min 18.446 avg 18.521 max 18.6 loss 0 | id 2AZxopbAtssvBnrLC00021UFj
HetznerFSN->Scaleway PAR | src Hetzner Online AS24940 Falkenstein,DE -> ping.online.net (51.158.1.21) | min 16.447 avg 16.545 max 16.623 loss 0 | id 2mwKdZyEaE49mNXiw00021UFj
HetznerFSN->Scaleway AMS | src Hetzner Online AS24940 Falkenstein,DE -> ping-ams1.online.net (163.172.208.7) | min 29.18 avg 29.276 max 29.515 loss 0 | id 2VrzSlLs1xEnqQYOz00021UFj
HetznerNBG->Scaleway AMS | src Hetzner Online AS24940 Nuremberg,DE -> ping-ams1.online.net (163.172.208.7) | min 29.616 avg 30.734 max 34.927 loss 0 | id 22eJVZ7yPkFQDekYY00021UFj
HetznerFSN->Leaseweb AMS | src Hetzner Online AS24940 Falkenstein,DE -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 11.177 avg 11.266 max 11.707 loss 0 | id 2SyAEKYFypFN6XRgJ00021UFj
HetznerNBG->Leaseweb AMS | src Hetzner Online AS24940 Nuremberg,DE -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 9.659 avg 10.27 max 12.172 loss 0 | id 2usuCsrGDBAmbcV5E00021UFj
HetznerFSN->Worldstream | src Hetzner Online AS24940 Falkenstein,DE -> speedtest.worldstream.nl (185.182.195.78) | min 12.022 avg 12.156 max 12.425 loss 0 | id 26rmXDMXmTqPqhqyz00021UFj
LeasewebAMS->Hetzner FSN | src LeaseWeb AS60781 Amsterdam,NL -> fsn1-speed.hetzner.com (78.46.170.2) | min 11.112 avg 11.187 max 11.276 loss 0 | id 2VmiafvUS1PiA8PVk00021UFj
WorldstreamNL->Hetzner FSN | src WorldStream AS49981 Rotterdam,NL -> fsn1-speed.hetzner.com (78.46.170.2) | min 12.739 avg 12.791 max 12.826 loss 0 | id 2RqxNsXgI5mFqWwbU00021UFj
WorldstreamNL->OVH RBX | src WorldStream AS49981 Rotterdam,NL -> rbx.proof.ovh.net (141.95.207.211) | min 8.021 avg 8.255 max 8.44 loss 0 | id 2TimVufGbKuWWqAPJ00021UFj
WorldstreamNL->OVH GRA | src WorldStream AS49981 Rotterdam,NL -> gra.proof.ovh.net (141.94.30.145) | min 7.852 avg 7.886 max 7.944 loss 0 | id 2ipuJ8G5gkJGLgt2G00021UFj
OVH GRA->Worldstream | src OVH AS16276 Gravelines,FR -> speedtest.worldstream.nl (185.182.195.78) | min 7.562 avg 7.589 max 7.641 loss 0 | id 2rS60t2k919EpegYs00021UFv
OVH RBX->Worldstream | src OVH AS16276 Roubaix,FR -> speedtest.worldstream.nl (185.182.195.78) | min 7.21 avg 7.298 max 7.355 loss 0 | id 2RtbzImOVdSHuHag600021UFv
ExoscaleZRH->Hetzner NBG | src Akenes AS61098 Zurich,CH -> nbg1-speed.hetzner.com (78.47.119.196) | min 8.416 avg 8.491 max 8.544 loss 0 | id 2HguYgbBBsEULgYU700021UFj
ExoscaleZRH->Hetzner FSN | src Akenes AS61098 Zurich,CH -> fsn1-speed.hetzner.com (78.46.170.2) | min 10.009 avg 10.065 max 10.178 loss 0 | id 2GnzX2UCctlonmYnu00021UFv
ExoscaleZRH->OVH SBG | src Akenes AS61098 Zurich,CH -> sbg.proof.ovh.net (51.91.75.40) | min 3.213 avg 3.281 max 3.368 loss 0 | id 27EbkaHA6Mzst0O2G00021UFv
ExoscaleZRH->OVH SBG (repeat) | src Akenes AS61098 Zurich,CH -> sbg.proof.ovh.net (51.91.75.40) | min 3.174 avg 3.243 max 3.333 loss 0 | id 28RwtzDMV3hV6Hhcq00021UFw
ExoscaleGVA->OVH SBG | src Akenes AS61098 Geneva,CH -> sbg.proof.ovh.net (51.91.75.40) | min 17.418 avg 17.469 max 17.604 loss 0 | id 27SKYy71SFJVWhCCX00021UFv
OVH SBG->cloudscale ZRH | src OVH AS16276 Strasbourg,FR -> www.cloudscale.ch (45.81.71.4) | min 3.764 avg 4.054 max 5.881 loss 0 | id 2NyFnmYBbqpFvbVv100021UFw
HetznerNBG->cloudscale ZRH | src Hetzner Online AS24940 Nuremberg,DE -> www.cloudscale.ch (45.81.71.4) | min 9.209 avg 9.445 max 9.774 loss 0 | id 2S2cyha9zBZnldgBK00021UFw
Init7 ZRH->OVH SBG | src Init7 (Switzerland) AS13030 Zurich,CH -> sbg.proof.ovh.net (51.91.75.40) | min 9.515 avg 9.59 max 9.758 loss 0 | id 2VnEoe78ADkXl0Vej00021UFw
Nine ZRH->OVH SBG | src Nine Internet Solutions AS29691 Zurich,CH -> sbg.proof.ovh.net (51.91.75.40) | min 4.219 avg 4.281 max 4.371 loss 0 | id 2b7Iqrfrb9lkhb2td00021UFw
ExoscaleZRH->cloudscale | src Akenes AS61098 Zurich,CH -> www.cloudscale.ch (45.81.71.4) | min 1.004 avg 1.053 max 1.14 loss 0 | id 2MfpgLA3wdQ8Fbb7Y00021UFw
OVH ZRH->OVH SBG | src OVH AS16276 Zurich,CH -> sbg.proof.ovh.net (51.91.75.40) | min 2.957 avg 3.015 max 3.048 loss 0 | id 2RkrhRluSSe5LkbgW00021UFw
InfomaniakGVA->cloudscale | src Infomaniak AS29222 Geneva,CH -> www.cloudscale.ch (45.81.71.4) | min 5.287 avg 5.352 max 5.461 loss 0 | id 2SBYuUNqOxF1csRNA00021UFw
InfomaniakGVA->OVH SBG | src Infomaniak AS29222 Geneva,CH -> sbg.proof.ovh.net (51.91.75.40) | min 7.426 avg 7.588 max 8.056 loss 0 | id 2Rqoo2tPvj9Jyp2aF00021UFv
InfomaniakGVA->OVH SBG | src Infomaniak AS29222 Geneva,CH -> sbg.proof.ovh.net (51.91.75.40) | min 7.481 avg 7.67 max 8.358 loss 0 | id 2Rqoo2tPvj9Jyp2aF00021UFv
InfomaniakGVA->Hetzner NBG | src Infomaniak AS29222 Geneva,CH -> nbg1-speed.hetzner.com (78.47.119.196) | min 11.998 avg 12.041 max 12.111 loss 0 | id 2RrsHv6BZb0xOJBmP00021UFv
InfomaniakGVA->Hetzner NBG | src Infomaniak AS29222 Geneva,CH -> nbg1-speed.hetzner.com (78.47.119.196) | min 11.536 avg 11.557 max 11.582 loss 0 | id 2RrsHv6BZb0xOJBmP00021UFv
InfomaniakGVA->Hetzner FSN | src Infomaniak AS29222 Geneva,CH -> fsn1-speed.hetzner.com (78.46.170.2) | min 13.792 avg 13.835 max 13.958 loss 0 | id 2V7tGkyZflPAQfnXu00021UFv
InfomaniakGVA->OVH GRA | src Infomaniak AS29222 Geneva,CH -> gra.proof.ovh.net (141.94.30.145) | min 17.837 avg 17.885 max 17.919 loss 0 | id 2i812fo91Ga7o28eI00021UFv
InfomaniakGVA->Scaleway PAR | src Infomaniak AS29222 Geneva,CH -> ping.online.net (51.158.1.21) | min 9.764 avg 9.82 max 9.973 loss 0 | id 2MLSIzXfcchna25ix00021UFv
OVH SBG->Infomaniak | src OVH AS16276 Strasbourg,FR -> www.infomaniak.com (185.125.25.1) | min 11.304 avg 11.341 max 11.472 loss 0 | id 2zVMfSMkYmQLk8cV700021UFv
HetznerNBG->Infomaniak | src Hetzner Online AS24940 Nuremberg,DE -> www.infomaniak.com (185.125.25.1) | min 11.905 avg 12.717 max 15.274 loss 0 | id 23owqxw8kjlr9Ue8W00021UFv
WaveComTLL->Hetzner HEL | src WaveCom AS34702 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 2.135 avg 2.203 max 2.249 loss 0 | id 2Dqq3hAQ2NIu3YqRu00021UFu
GleSYS STO->Hetzner HEL | src Glesys Sweden AS42708 Stockholm,SE -> hel1-speed.hetzner.com (95.217.255.81) | min 7.911 avg 8.016 max 8.309 loss 0 | id 2jSefMsyiZCnUuY6900021UFu
Bahnhof STO->Hetzner HEL | src Bahnhof AS8473 Stockholm,SE -> hel1-speed.hetzner.com (95.217.255.81) | min 7.625 avg 7.691 max 7.756 loss 0 | id 23z9IgvCYyEpLGfqK00021UFv
UpCloud STO->Hetzner HEL | src UpCloud AS202053 Stockholm,SE -> hel1-speed.hetzner.com (95.217.255.81) | min 6.52 avg 6.582 max 6.67 loss 0 | id 2sCBFsXYYyyCIdUly00021UFv
UpCloudHEL->Hetzner HEL | src UpCloud AS202053 Helsinki,FI -> hel1-speed.hetzner.com (95.217.255.81) | min 1.028 avg 1.091 max 1.226 loss 0 | id 2URDzUHt3DPP7jEpf00021UFv
CherryLT->Hetzner HEL | src Cherry Servers AS16125 Siauliai,LT -> hel1-speed.hetzner.com (95.217.255.81) | min 39.627 avg 39.683 max 39.713 loss 0 | id 2GBuRh8WSx9ehaLsZ00021UFv
1984 RKV->Hetzner HEL | src 1984 AS44925 Reykjavik,IS -> hel1-speed.hetzner.com (95.217.255.81) | min 67.4 avg 67.506 max 67.796 loss 0 | id 2fU8JtkgElJ9iJmZ900021UFv
```

## Appendix B — Exchange membership (PeeringDB, fetched 11 Nov 2026)

Source: `https://www.peeringdb.com/api/netixlan` and `https://www.peeringdb.com/api/net`, filtered by network number. Port totals are the sum of listed ports.

| Network | Policy | Largest exchange ports | Shared with its partner in the pairs above |
|---|---|---|---|
| Hetzner (AS24940) | Open | DE-CIX Frankfurt 2,800 Gbit/s; AMS-IX 800; FICIX Helsinki and Espoo 100 each | With OVHcloud: DE-CIX Frankfurt, AMS-IX, NL-ix, France-IX Paris, LINX, VIX, NIX.CZ, Peering.cz, Netnod Stockholm and others. With WaveCom: none. With Infomaniak: none |
| OVHcloud (AS16276) | Open | DE-CIX Frankfurt 1,600; AMS-IX 1,600; LINX 800; France-IX Paris 400; SwissIX 100 | With Infomaniak: SwissIX. With Worldstream: AMS-IX, NL-ix, DE-CIX Frankfurt, Frys-IX, Speed-IX, ERA-IX Amsterdam, Peering.cz, 1-IX EU |
| WaveCom (AS34702) | Open | RTIX 80 | |
| Infomaniak (AS29222) | Open | SwissIX 120; CIXP 40 | |
| Worldstream (AS49981) | Open | AMS-IX 800; NL-ix 800 | |
| netcup (AS197540) | "No" | no exchange rows | none listed |

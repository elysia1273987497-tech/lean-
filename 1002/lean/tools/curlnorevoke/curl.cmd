@echo off
REM Thin curl wrapper: injects --ssl-no-revoke so Windows schannel does not fail
REM on CRL/OCSP revocation checks (which the local VPN/proxy environment cannot complete).
REM The Mathlib cache tool invokes `curl`; put this directory first on PATH to use it.
"C:\Users\12739\anaconda3\Library\bin\curl.exe" --ssl-no-revoke %*

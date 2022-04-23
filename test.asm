; MMIO:
;  - 0x80: 1
;  - 0x81: 0
;  - 0x82: RR
;  - 0x83: !RR

; Initialize the CPU
IEN 0x80    ; Enable input
OEN 0x80    ; Enable output
ONE         ; Result ALU
LD 0x81     ; Load 0 into RR

LD 0x80     ; Load Op1 Bit1 into RR
ADD 0x80    ; Add Op2 Bit1 to RR
STOC 0x00   ; Store !RR to RAM

LD 0x81     ; Load 0 into RR
ADD 0x81    ; Add 0 to RR (move Carry to RR)
STO 0x1     ; Store RR to RAM

NAND 0x80   ; NAND RR with 1
OEN 0x82    ; Disable OEN if RR is 0
LD 0x80
STO 0x3     ; Save to RAM. Write should be suppressed
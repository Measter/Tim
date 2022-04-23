#DEF MMIO_ZERO  = 0x80
#DEF MMIO_ONE   = 0x81
#DEF MMIO_RR    = 0x82
#DEF MMIO_RRQ   = 0x83

; Initialize the CPU
IEN     MMIO_ONE    ; Enable input
OEN     MMIO_ONE    ; Enable output
ONE                 ; Reset ALU
LD      MMIO_ZERO   ; Load 0 into MMIO_RR

LD      MMIO_ONE    ; Load Op1 Bit1 into MMIO_RR
Add     MMIO_ONE    ; Add Op2 Bit1 to MMIO_RR
STOC    0x00        ; Store !MMIO_RR to RAM

LD      MMIO_ZERO   ; Load 0 into MMIO_RR
ADD     MMIO_ZERO   ; Add 0 to MMIO_RR (move Carry to RR)
STO     0x1         ; Store MMIO_RR to RAM

NAND    MMIO_ONE    ; NAND MMIO_RR with 1
OEN     MMIO_RR     ; Disable OEN if RR is 0
LD      MMIO_ONE
STO     0x3         ; Save to RAM. Write should be suppressed
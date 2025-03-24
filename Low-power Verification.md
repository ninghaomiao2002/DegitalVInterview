# Low-power Verification

# Techniques:

- **gating**:
    - **clock gating** - disables the **clock signal** to unused logic
        - verification:
            - gating is correct - **clock gating check tool** to report missing clock gate
            - power is reduced when clock gating is active
            - functions are correct - functional
            - enable is back to low, the gate_clock is equal to clock - formal
            
            ```verilog
            property clock_gating_property;
                @(posedge clk) (enable) |-> (gated_clk == clk);
            endproperty
            assert property (clock_gating_property);
            ```
            
    - **power gating** - turns off the **power supply** to unused logic
        - problems - solutions:
            - data will lose or corrupt in FF - retention logic
            - signal from power OFF → ON might not be valid - isolation logic
        - Verification:
            - **Retention logic** works - state saved at OFF and restored at ON
            - **Isolation logic** works - isolation cells clamp the output when the source domain is OFF
- **DVFS** - dynamic voltage and frequency scaling:
    - low power and frequency - low performance
    - high power and frequency - high performance
    - Verification:
        - DVFS need to be valid
        - **cross power domain or clock domain may lead metastability and** glitches - formal

# Interview Questions

1. **What is UPF (Unified Power Format) and why is it important?**
- An **industry-standard power management format** used to define **power intent** in digital IC design
- Features:
    - power domains
        - own power supply
        - own low-power design strategies
            - power gating
            - voltage scaling
            - state retention
    - power states
        - on
        - off
        - retention - logic off, state retained
        - sleep - clock fated
    - power control signals(clock gating signals)
    - correct low-power behavior in simulation and synthesis

1. **How do you verify power domain crossings(PDC)?**
- Power Domain Crossing (PDC) occurs when **a signal crosses from one power domain to another** with **different voltage levels or power states**.
- Cause:
    - **Glitches and metastability**(if synchronization is missing).
    - **Data corruption** (if voltage levels are incompatible).
- Methods:
    - UPF to check RTL
    - SVA(Formal) to check data matches or not

1. **What is clock gating, and how do you verify it?**
- A **low-power design technique** that reduces dynamic power consumption by disabling the clock signal to inactive parts of a circuit.
- How to verify?
    - clock gating is correct
        - clock gating check tool to report missing clock gate
    - checks if power is reduced when clock gating is active
    - check if functions are correct - functional verification
    - check when enable is high, the gate_clock is equal to clock - Formal

1. **Explain retention flops and their verification challenges.**
- special **flip-flops that retain their state** even when their power domain is turned **off**
- Used during **low-power or sleep modes**
- How they work?
    - Normal FF when powered
        - When entering retention mode:
            - Value is **saved to retention latch**
            - Core logic is powered off
        - On power-up:
            - Value is **restored** from retention latch
- Verification Challenges:
    - Retention Value Integrity
        - Before shutdown: value must be saved
        - After wake-up: value must be restored correctly
        - Use assertions to compare pre- and post-power-down values
    - Incorrect Power Gating Timing
        - If power gating is applied **before the value is retained**, you lose data.
        - Add assertions to check retention save timing relative to power-down

1. **How does DVFS (Dynamic Voltage Frequency Scaling) impact verification?**
- **DVFS (Dynamic Voltage and Frequency Scaling)** is a **power management technique** where a system **adjusts voltage and clock frequency at runtime** based on performance or power needs.
    - **Higher performance = higher voltage + higher frequency**
    - **Low power = lower voltage + lower frequency**
- How DVFS Impacts Verification？
    - DVFS must be valid
    - **complex CDC** scenarios introduce complexity
    - glitches, metastability, or incorrect behavior
1. **How do you simulate multiple power states in an SoC?**
- Define power domain and states in UPF
- Specify Isolation and Retention Logic
- Simulate Transitions Using a Testbench
- Use Power-Aware Simulators with UPF
- Verify functionality, retention, isolation, transitions

1. **How do you verify that a power domain transition does not cause data corruption?**
- SVA to check pre-transition and post-transition

1. **What are the key challenges in verifying multi-power domain designs?**
- power state transition - no metastability and glitch
- isolation logic verification - ensure power OFF logic does not drive invalid data
- retention logic verification - track pre- and post-transition values
- Clock Domain Crossing (CDC) Between Power Domains - use synchronizers and formal

1. What does Isolation mean?
- **Isolation** refers to **preventing signal corruption** when one **power domain is turned OFF** and it's still connected to an **active domain**
- Power Domain A (OFF) → drives signals into → Power Domain B (ON)
    - A's logic is OFF, so its outputs are undefined (floating or X)
    - Without isolation, B could receive **garbage data**, leading to **functional errors or simulation mismatches**
- Method:
    - Isolation Cells
        - Inserted **at the boundary** of a power domain
        - clamp the output when the source domain is OFF
1. **How do you check isolation logic between power domains?**
- The **isolation enable signal (`iso_en`)** behaves correctly
- Isolation cells are **inserted at correct boundaries**
- Outputs from OFF domains are **clamped** (e.g., to 0 or 1)
- No **X-propagation**, glitches, or incorrect logic from OFF domains
- Methods:
    - UPF simulator
    - SVA for **X-propagation**, glitches, or incorrect logic and Outputs from OFF domains are **clamped**
1. **What low-power checks can you implement using assertions?**
- isolation: check no X signals outputs for OFF domains
- DVFS:
- Clock Gating: if clock signal come back normally after clock gating
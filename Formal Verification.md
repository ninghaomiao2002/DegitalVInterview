# Formal Verification

# Interview Questions

1. What is the difference between **immediate** and **concurrent assertions**?
- **immediate assertions**
    - **Evaluated once** at the time of execution(like initial)
    - Used inside **procedural blocks** (`always`, `initial`, `forever`, `task`, etc.).
    - Executes like a regular **if statement**.
    - example:
    
    ```verilog
    always @(posedge clk) begin
        assert (alu_result != 0) else $error("ALU result is zero!");
    end
    //Checks the condition at each clock edge and reports an error if alu_result is zero.
    ```
    
- concurrent assertions
    - **Evaluated over multiple clock cycles**.
    - Used for checking **temporal properties** (sequences of events).
    - Must be placed **outside procedural blocks** or in **`always` or `initial` blocks** with `disable iff`.
    - example:
    
    ```verilog
    property handshake;
        @(posedge clk) req |=> ack; // If `req` is high, `ack` must be high in the next cycle
    endproperty
    assert property(handshake);
    ```
    

1. Explain the different types of **properties** in SVA.

| Property Type | Purpose | **Example** |
| --- | --- | --- |
| Boolean Property | Simple Boolean expressions that evaluate in a single cycle | `data_valid && enable` |
| Implication Property | overlapping and not overlapping | `|→` and `|=>` |
| Sequence Property | Defines an ordered series of events over multiple clock cycles | `@(posedge clk) (a ##1 b ##2 c);` |
| Disabling Property | disable reset | `@(posedge clk) disable iff (reset) (req |-> ##1 ack);` |

1. What are `|->` and `|=>` in assertions?
- **`|->`: Overlapping Implication**
    - If `a` is true, `b` must be **true in the same cycle**.
- `|⇒`: **Non-Overlapping Implication**
    - If `a` is true in cycle **N**, `b` must be true in cycle **N+1**.

```verilog
**property compare;
	(@posedge clk) assert a |-> b; //Overlapping Implication
	(@posedge clk) assert a |=> c; //Non-Overlapping Implication
endproperty

a: assert property(compare);**
```

1. **How do you write an assertion to check that a request (req) is acknowledged (ack) within 3 clock cycles?**

```verilog
property ack_check;
(@posedge clk) req **|-> ##[1:3] ack;
endproperty

a: assert property(**ack_check);
```

1. **What is a sequence in SVA, and how do you use it inside an assertion?**

```verilog
sequence abc;
	a ##1 b ##3 c ##[1:3] d;
endsequence;

property seq_check;
	abc;
**endproperty

a: assert property(**seq_check);
```

1. **Explain $rose(signal), $fell(signal), and $stable(signal).**

| Function | Meaning | Behavior |
| --- | --- | --- |
| `$rose(signal)` | Detects rising edge | Returns `1` if `signal` changes from `0 → 1` |
| `$fell(signal)` | Detects falling edge | Returns `1` if `signal` changes from `1 → 0` |
| `$stable(signal)` | Detects no change | Returns `1` if `signal` remains the same |

```verilog
property compare;
	(@posedge clk) $rose(a);
	(@posedge clk) $fell(b);
	(@posedge clk) $stable(c);
endproperty;

a: assert property(compare);
```

1. What is a `disable iff` construct in an assertion?

The **`disable iff`** construct in **SVA** is used to **disable or ignore** an assertion when a specified condition (typically a reset signal) is active.

```verilog
property check;
	(@posedge clk) disable iff (reset) a **|=> b;**
endproperty;

a: assert property(check);
```

1. How can you use assertions to detect protocol violations in AMBA (AXI, AHB) interfaces?
- AMBA - **Advanced Microcontroller Bus Architecture**, a freely available, **open standard** for the **connection and management** of functional blocks in a System-on-Chip (SoC)
    - AXI - **Advanced eXtensible Interface**
    
    | Channel | Purpose | **Key Signals** |
    | --- | --- | --- |
    | Write Address(AW) | Sends write request address | `AWADDR`, `AWVALID`, `AWREADY` |
    | Write Data(W) | Sends data to be written | `WDATA`, `WVALID`, `WREADY` |
    | Write Response(B) | Confirms write completion | `BVALID`, `BREADY` |
    | Read Address(AR) | Sends read request address | `ARADDR`, `ARVALID`, `ARREADY` |
    | Read Data(R) | Returns read data | `RDATA`, `RVALID`, `RREADY` |
    
    ```verilog
    property axi_aw_handshake;
        @(posedge ACLK) disable iff (!ARESETn)
        AWVALID |-> ##[1:$] AWREADY;
    endproperty
    assert property (axi_aw_handshake);
    ```
    
    - AHB - **Advanced High-Performance Bus**
    
1. **How do you check for sequential dependencies between signals?**
- **Sequential dependencies** define **cause-and-effect relationships between signals over multiple clock cycles**.
    - A specific signal change **triggers another signal after a defined delay**
    - A certain **order of events is followed**(sequence)
    - Timing **constraints between signals are met**
- Methods:
    - Using Implication Operators **`|->` and** `|⇒`
    
    ```verilog
    property req_to_ack;
        @(posedge clk) req |=> ack;
    endproperty
    
    assert property (req_to_ack);
    ```
    
    - Using Sequences
    
    ```verilog
    sequence req_grant_seq;
        req ##2 grant; // `grant` occurs exactly 2 cycles after `req`
    endsequence
    
    property req_to_grant;
        @(posedge clk) req_grant_seq;
    endproperty
    
    assert property (req_to_grant);
    ```
    

1. What are cover properties in SVA, and how do they differ from assertions?
- A **cover property** in **SVA** is used to **track when a specific sequence of events occurs in a simulation**.

|  | Assertions  | Cover Properties |
| --- | --- | --- |
| Checks Correctness? | ✅ | ❌ |
| Reports Errors? | ✅ | ❌ |
| Stops Simulation? | ✅ | ❌ |
| **Used for Coverage?** | ❌ | ✅ |

1. What is the difference between **simulation-based verification** and **formal verification**?
- **Simulation-Based Verification**: Uses **testbenches** and **stimulus-driven simulations** to validate design behavior over time.
- **Formal Verification**: Uses **mathematical proofs and formal methods** to check correctness under all possible inputs.

1. What are the **advantages** and **limitations** of formal verification?
- Pros:
    - Verifies all possible input conditions, not just test cases
    - No need for testbench
    - 100% coverage
    - better for logic designs(protocols, FSM)
- Cons:
    - Big model with many states will consume a huge amount of time
    - **high memory and processing power** for large designs

1. What are **vacuous** passes in formal verification, and how do you avoid them?
- A vacuous pass indicates that the property is structurally correct but is not being triggered in the design.

```verilog
property req_ack_check;
    @(posedge clk) req |=> ack;
endproperty

assert property(req_ack_check);
cover property(req_ack_check);
```

- use **cover** to check if it is triggered

1. Explain **bounded model checking(BMC)** and how it is used in formal verification.
- **Bounded Model Checking (BMC)** is a **formal verification technique** that checks whether a property holds **within a fixed number of cycles (N)**. Instead of proving correctness for **all possible states**, BMC explores **all reachable states within a bounded depth** and finds counterexamples if the property fails.
- BMC is fast but does not guarantee full correctness unless `N` is large enough to cover all reachable states.
- trade-offs:

| Feature | Bounded Model Checking (BMC) | Unbounded Model Checking (UMC) |
| --- | --- | --- |
| Proof Guarantee | Only with `N` cycles | Ensures correctness for all cycles |
| Computational Complexity | Lower (bounded exploration) | Higher |
| Finds Bugs? | Quickly detects shallow bugs | Detects all bugs but may be slow |
| Handles Large Designs? | Yes | Limited by state explosion |
| Common Use Case | Bug detection in pipelined circuits, protocols | Proving correctness of small state machines |

1. What is an **assume-guarantee relationship** in formal verification?
- The **assume-guarantee (A-G) relationship** is a **modular verification technique** in **formal verification**. It is used to **break down complex system verification into smaller, manageable parts** by defining **assumptions on one module and guarantees on another**.

1. What is **induction** in formal verification, and why is it useful?
- Induction in **formal verification** is a proof technique used to **establish that a property holds for all cycles** in a design(Invariant)
- **Base Case (`k=0`)** + **Inductive Step (`k → k+1`)**

1. How do you handle **state explosion** in formal verification?
- **State explosion** occurs in **formal verification** when the number of possible states in a design **grows exponentially**, making verification computationally expensive or infeasible.
- Use **Assume-Guarantee Reasoning**
- Use **Bounded Model Checking**

```verilog
property high_way_control_check;
    @(posedge clk) 
    (E9 && (state == "Highway Control")) |=> (state == "Collision Avoidance");
endproperty

high_way_control_cover_1: cover property(high_way_control_check);
high_way_control_check_1: assert property(high_way_control_check);

```

1. What is equivalence checking in formal verification?
- Equivalence checking is a formal verification technique that compares two versions of a design (e.g., pre-synthesis RTL and post-synthesis netlist) to ensure they are functionally identical, confirming that synthesis or optimizations have not introduced errors.
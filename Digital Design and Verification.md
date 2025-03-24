# Digital Design and Verification

# Interview Questions

1. What does **simulation**, **synthesis** and **implementation** do?
- Simulation uses software to run Verilog/SV code.
- Synthesis convert HDL(Hardware Description Language) into Gat-Level Netlist.
- Implementation converts Gate-Level Netlist to hardware layout(FPGA).

1. Blocking statement `=` and Non-blocking statement `<=`.
- Blocking Statement:
    - **Executes immediately**, in **sequence** (like regular software code).
    - "Blocks" the next statement until it completes.
    - Commonly used in **combinational logic** or **testbenches**.

```verilog
reg a = 0;
reg b = 1
always @(*) begin
  a = b; //a = 1
  b = a; //b = 1
end
```

- Non-blocking statement:
    - **Schedules** the update to happen **at the end of the time step**.
    - **Does not block** execution of the next statement.
    - Essential for **synchronous (clocked) logic**.

```verilog
reg a = 0;
reg b = 1;

always @(*) begin
  a <= b; //a = 1
  b <= a; //b = 0
end
```

1. **Synchronous and Asynchronous.**
- **Synchronous** circuits rely on a common clock signal to synchronize the flow of data.

```verilog
always (@posedge clk) begin
	if (reset) begin
		a <= 0;
	end else begin
		a <= b + c;
	end
end
```

- **Asynchronous** circuits don’t rely on a central clock, allowing for more flexibility in their operation.

```verilog
always (@posedge clk or posedge reset ) begin
	if (reset) begin
		a <= 0;
	end else begin
		a <= b + c;
	end
end
```

1. `reg`  ,`wire` and `logic`
- `wire`:
    - **Combinational connections** between modules or within a module.
    - Driving values **from continuous assignments** (`assign`) or **output ports**.
- `reg`:
    - Verilog only
    - Holding a value inside **procedural blocks**
- `logic`:
    - Replaces both `reg` and `wire` for **most purposes**.
    - Does **not allow multiple drivers** like `wire`
1. Difference between **Verification** and **Validation**.
- In a verification flow the correctness of the design is being tested against the design specifications.
- In the validation flow the correctness of the design is being tested against the needs of the targeted user.

1. What is RISC-V and its Pros and Cons.
- RISC - Reduced Instruction Set Computer
- Pros:
    - Open source and free
    - **Simplicity**
    - avoid unnecessary complexity
    - specific tasks
- **Cons:**
    - **Limited software ecosystem** (vs ARM/x86)
    - lack support
1. Difference between `Task` and `Function`

| Feature | Function | Task |
| --- | --- | --- |
| Purpose | compute and return a value | executing a sequence of actions |
| Timing Control | ❌ | Can include delays (`#`, `@`, `wait`) |
| Inputs/Outputs | Only **input** arguments allowed | Can have **input, output, inout** arguments |
| **Reentrant?** | ✅ | ✅ |

1. `fork…join`, `fork…join_any` and `fork…join_none`

```verilog
//fork...join
initial begin
  fork
    #5 $display("A done");
    #10 $display("B done");
  join
  $display("Both A and B finished");
end
//display
//A done
//B done
//Both A and B finished

//fork...join
initial begin
  fork
    #5 $display("A done");
    #10 $display("B done");
  join_any
  $display("One of A or B finished");
end
//display
//A done
//One of A or B finished
//B done

//fork...join_none
initial begin
  fork
    #5 $display("A done");
    #10 $display("B done");
  join_none
  $display("Continue immediately");
end
//display
//Continue immediately
//A done
//B done
```

1. What is **regular expression** and why it is important in verification process?
- A **pattern-matching language** used to search, match, or manipulate strings of text
- regular expression is **crucial** in modern hardware verification for **flexibility, automation, and powerful pattern matching**
1. Test Plan, Testcase, Testbench difference.
- Test Plan: A **test plan** is a **document** that outlines:
    - What to be verified
    - How to be tested
    - Coverage goals
- Testcase:
    - Applies stimulus to the DUT
    - Monitors outputs
    - Checks for correctness
- Testbench: the **hardware simulation environment** that wraps around your **Design Under Test (DUT)** and includes:
    - Stimulus generation
    - DUT instantiation
    - Monitors, checkers, scoreboards
    - Assertions and coverage logic

1. What is metastability and how to avoid?
- a signal reach undefined or unstable state in violating setup time or hold time
- When does it happen?
    - **Asynchronous signal sampling**
    - **Clock domain crossing** (CDC)
    - **Unsynchronized inputs from the external world** (buttons, sensors, etc.)
- How to prevent?
    - **Double or triple flip-flop synchronizers**
    - Proper setup/hold timing analysis

1. What is glitch and metastability?
- glitch: **timing mismatches** or **logic hazards** in a digital circuit
    - solution:
        - Use proper synchronizers
        - Static timing analysis

```verilog
assign y = a & b | c;
//If a and b change together, but due to delay differences one reaches the gate earlier than the other, y might glitch temporarily even if logically correct in the end.
```

- metastability: a **flip-flop** or **latch** enters an **unstable, undefined logic state**—**neither 0 nor 1**—due to a violation of its **timing constraints** (specifically, **setup or hold time**).
    - solution:
        - Synchronizer
        - Clock Domain Crossing FIFOs
1. What is race and risk?
- race: **two or more signals** compete to change a variable, one could arrive before than another one

```verilog
initial begin
  a = 1;
  b = 0;
end

always @(a)
  b = 1;

always @(a)
  b = 2;

```

- risk: cause metastability and glitch
- solution:
    - Synchronizers
    - Handshake protocols
    - Clock gating / isolation
    - Formal verification / assertions

1. `always_ff`, `always_comb` and `always`
- `always_ff` :
    - For **Sequential Logic**
    - **must** contain only clock/reset signals
    
    ```verilog
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 0;
        else
            q <= d;
    end
    ```
    
- `always_comb`:
    - For **Combinational Logic**
    
    ```verilog
    always_comb begin
        y = a & b;
    end
    ```
    
- `always`:
    - General Purpose
    
    ```verilog
    always @(posedge clk or posedge reset) begin
        // Can be sequential logic
    end
    
    always @(*) begin
        // Can be combinational logic
    end
    ```
    

1. FPGA, ASIC, CPU, GPU, NPU difference.
- **FPGA(Field-programmable Gate Array):** a configurable integrated circuit which can be repeatedly programmed after manufacturing
- **ASIC(Application Specific Integrated Circuit):** an integrated circuit that implements a specific function
- **GPU(Graphics Processing Unit): 
• Excellent at tasks that can be parallelized**
• Machine Learning
• Graphics rendering
- **NPU(Neural Processing Unit)**: optimized for artificial intelligence (AI) neural networks, deep learning and machine learning tasks and applications
- **CPU**(**Central Processing Unit):**
    - General-purpose computing tasks
    - Excellent at single-threaded performance
1. What is Static Timing Analysis(STA)?
- setup time: The minimum time before the clock edge that data must be stable.
- hold time: The minimum time after the clock edge that data must remain stable.
- **Critical Path**: The longest delay path in the circuit, which determines the maximum clock frequency.
- **Clock Skew**: The difference in arrival time of the clock signal at different flip-flops.
- **Slack**: The difference between the required time and the actual arrival time of a signal.

1. Gate
- AND
- OR
- NOT
- NAND
- NOR
- XOR

1. Bus
- a **shared communication pathway** that allows multiple components in a system (like CPUs, memory, and peripherals) to **transfer data, addresses, and control signals** with one another
- types:
    - data bus
        - carry data
    - address bus
        - carry memory address
    - control bus
        - Carries control signals
- AXI - **high-performance**, **highly flexible**, and **pipelined** bus protocol
    - channels:
        - read data(R) - slave → master
            - slave assert valid → master assert ready → transfer
        - read address(AR) - master → slave
            - master assert valid → slave assert ready → transfer
        - write data(W) - master → slave
            - master assert valid → slave assert ready → transfer
        - write address(AW) - master → slave
            - master assert valid → slave assert ready → transfer
        - write response(B) - slave → master
            - slave assert valid and resp → master assert ready → result of the write

1. what is macro?
- allows for text substitution

```verilog
`define DL1WAYS 4
`define WIDTH 10
```

1. How does functional verification differ from timing verification?

| Feature | Functional Verification | Timing Verification |
| --- | --- | --- |
| Checks | Logical behavior | Temporal/delay constraints |
| Common Tools | UVM, Formal | STA tools |
| Based on | Simulation or formal models | Gate-level netlist + timing libs |
| Goal | right? | on time? |

1. What are the different levels of abstraction used in verification?

| Abstraction Level | Language(s) | Used For |
| --- | --- | --- |
| Algorithmic / Behavioral | C, C++, Python | Early modeling |
| TLM | SystemC | SoC-level |
| RTL | SystemVerilog | Functional verification |
| Gate-Level | Verilog | Timing and post-synthesis checks |

1. What is the difference between a simulator and an emulator?

| Feature | Simulator | Emulator |
| --- | --- | --- |
| Runs On | Software (CPU-based) | Dedicated hardware (FPGAs, ASICs) |
| Speed | Slow  | faster  |
| Capacity | Small to medium designs | Large, full-chip SoC |

1. Explain the use of interfaces in SV.
- An **interface** is a **container for signals and methods** that are commonly shared between modules or between DUT and testbench components.
- Why needed?
    - Avoid repeating long signal lists in module ports
    - Centralize bus or protocol definitions
    - Allow encapsulation of protocol behavior

```verilog
interface sample;
	logic clk;
	logic reset;
	logic a;
	logic b;
	logic c;
endinterface

module mydut(sample intf);
	always_ff (@posedge intf.clk) begin
		intf.a <= 1;
	end
endmodule

module tb;
	sample sintf();
	mydut dut(.intf(sif));
	
	initial begin
		sif.clk = 0;
		forever #5 sif.clk = ~sif.clk;
	end
endmodule
```

1. Moore and Mealy state machines
- **Moore**: Output = `f(state)`
- **Mealy**: Output = `f(state, input)`

1. Is run phase top down/bottom up?
- `build_phase`: top-down
- `connect_phase`: top-down
- `run_phase`: bottom-up

1. FF Verilog code

```verilog
module ff(input clk, input reset, input d, output q);
	
	always (@posedge clk or negedge reset) begin
		if (reset) begin
			q <= 0;
		end else if
			q <= d;
		end
	end

endmodule
```
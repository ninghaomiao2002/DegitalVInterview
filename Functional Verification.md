# Functional Verification

# Interview Questions

1. **What are the key components of a UVM testbench?**
- **agent**
    - **sequencer** - generates data transactions and send to driver
    - **driver** - drives signals to interface
    - **monitor** - captures signals from interface and translates into transaction level data to be sent to other components.
- **scoreboard -** verifies the functionality of a design
    - **reference model** - also called predictor, predict the expected value
    - **checker** - compare between reference model and monitor
- **Coverage Collector**
- Subscriber - listen analysis port

1. What is Transaction-Level Modeling (TLM)?
- **TLM(Transaction-Level Modeling)** is a **high-level communication method** used in UVM and SystemVerilog to pass **data transactions between components** instead of using low-level signal toggling.
- Pros:
    - Instead of driving **individual signals (like `clk`, `addr`, `data`)**, TLM **transfers entire transactions** between testbench components
    - Uses **TLM interfaces (ports, exports, FIFOs)** for efficient communication
    - Reduces **testbench complexity** and improves **simulation speed**
- Example:

```verilog
//send individual signals to the DUT:
addr = 32'hA000_0000;
data = 32'hDEAD_BEEF;
valid = 1;
//send a TLM transaction
txn.addr = 32'hA000_0000;
txn.data = 32'hDEAD_BEEF;
ap.write(txn);
```

- TLM vs RTL:

| Aspect | RTL(Verilog or SV) | TLM (SystemC) |
| --- | --- | --- |
| Abstraction level | Signal-level | Transaction-level |
| Communication | Wires, signals | Function calls / method |
| Simulation speed | Slow | faster |
| Typical use | Final design & verification | Early architecture exploration |

3.  **Explain the different phases in UVM.**

- Build phase
    - build - build testbench components and create their instances
    - connect - connect between different **testbench components** via TLM ports
    - end_of_elaboration - processes and expands the design hierarchy before simulation or synthesis
    - start_simulation - set initial run-time configuration or display topology
- Run phase
    - run - simulation that consumes time happens in this UVM phase and runs parallel to other UVM run-time phases
- clean-up phase
    - extract - extract expected data from scoreboard
    - check - perform scoreboard and check errors
    - report - report results

1. **How do you write a sequence in UVM, and how does it interact with the driver?**
- UVM sequence is a mechanism for generating stimulus in UVM testbench
- defines how stimulus are generated and send to driver via sequencer

1. What is a Virtual Sequence in UVM?
- A **normal sequence** runs on a single sequencer.
- A **virtual sequence** controls **multiple sequences across different sequencers**.

1. **How does the UVM factory mechanism work, and why is it useful?**
- The **UVM factory** is a centralized mechanism that manages the **creation (instantiation)** of UVM objects and components (like `uvm_object`, `uvm_component`, etc.).

```verilog
`uvm_object_utils(my_class)         // for uvm_object-based types
`uvm_component_utils(my_component) // for uvm_component-based types
//Instead of:
my_component comp = new("comp", parent);
//You write:
my_component comp;
comp = my_component::type_id::create("comp", parent);

```

- Why important?
    - Reusability - Swap in different implementations (e.g., drivers, monitors) without modifying the base testbench
    - Test Configurability - Tests can configure which components or objects to use via factory overrides
    - Cleaner Code - Centralized control over instantiation and overrides
1. Explain UVM objections. How do you raise and drop objections in a test?
- UVM objections - a mechanism that prevents simulation phase from ending until all components have been completed.

```verilog
class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting test sequence");
        `uvm_info("TEST", "Objection raised - Test Running", UVM_MEDIUM)

        #100; // Simulate test running

        phase.drop_objection(this, "Ending test sequence");
        `uvm_info("TEST", "Objection dropped - Test Ending", UVM_MEDIUM)
    endtask
endclass

```

1. **How do you measure functional coverage in UVM?**
- **Code coverage** - checks which lines/branches in RTL were executed
- **Functional coverage** - follow specification for conditions, could be checked in scoreboard or minitor
    - covergroup
    - coverpoint
    - bins
    
    ```verilog
    covergroup addr_coverage;
        coverpoint addr {
            bins low = {0};      // Single value bin for 0
            bins mid = {[10:20]}; // Range bin for values 10-20
            bins high = {255};   // Bin for max value
        }
    endgroup
    //This tracks how many times addr takes values in {0, 10-20, 255}.
    ```
    
    - Example:

```verilog
class my_monitor extends uvm_monitor;
    `uvm_component_utils(my_monitor)

    uvm_analysis_port#(my_transaction) ap;  // Sends transactions to scoreboard
    virtual dut_if vif;  // Virtual interface

    covergroup my_coverage;
        coverpoint vif.addr { bins addr_bins[] = {8'h00, 8'hFF}; } // Edge cases
        coverpoint vif.data { bins low = {8'h00}; bins high = {8'hFF}; } // Min/Max values
        cross vif.addr, vif.data; // Cross-coverage between addr and data
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        my_coverage = new(); // Create covergroup instance
    endfunction

    virtual function void build_phase(uvm_phase phase);
        if (!uvm_config_db#(virtual dut_if)::get(this, "", "vif", vif))
            `uvm_fatal("MONITOR", "No virtual interface provided")
    endfunction

    task run_phase(uvm_phase phase);
        my_transaction txn;
        forever begin
            @(posedge vif.clk);
            txn = new();
            txn.addr = vif.addr;
            txn.data = vif.data;
            ap.write(txn); // Send to scoreboard
            my_coverage.sample(); // Sample coverage
        end
    endtask
endclass

```

1. **What is the difference between analysis ports(uvm_analysis_port) and TLM FIFOs?**
- **`uvm_analysis_port` is a broadcast mechanism** (used in monitors & scoreboards).
- **`uvm_tlm_fifo` is a queue mechanism** (used in sequencer-driver communication).

1. How to Use UVM Configuration Database (`uvm_config_db`)
- The **UVM Configuration Database (`uvm_config_db`)** is a mechanism for **storing and retrieving configuration objects, handles, or values** between UVM components.
    - **Key Features:**
        - **Passes configurations from parent to child components**.
        - **Stores handles to virtual interfaces (`vif`)**.
        - **Eliminates hardcoded connections**, making testbenches reusable.
        - **Can store simple values (integers, strings) or complex objects (virtual interfaces, parameters, configurations).**

1. Difference Between `uvm_component` and `uvm_object` in UVM.

| Feature | `uvm_component` | `uvm_object` |
| --- | --- | --- |
| Hierarchy | Exists in the UVM testbench hierarchy (has a parent-child relationship). | Does **not** belong to the UVM hierarchy.

 |
| Phases | driver, monitor, sequencer, agent, scoreboard | **No phase execution**, only data storage. |
| Use Case | Used for **testbench components** (e.g., driver, monitor, sequencer, agent, scoreboard). | Used for **transactions, sequences, configuration objects**.
 |
| Instantiation | Created using `type_id::create()` and **needs a parent component**. | Created using `new()`, **does not require a parent** |
1. OOP Example
- Inheritance

```verilog
// Code your testbench here
// or browse Examples
class Packet;
   int addr;

   function new(int addr);
      this.addr = addr;
   endfunction

	function display();
		$display ("[Base] addr=0x%0h", addr);
	endfunction
endclass

// A subclass called 'ExtPacket' is derived from the base class 'Packet' using
// 'extends' keyword which makes 'EthPacket' a child of the parent class 'Packet'
// The child class inherits all variables and methods from the parent class
class ExtPacket extends Packet;

	// This is a new variable only available in child class
	int data;

   function new(int addr, data);
      super.new (addr); 	// Calls 'new' method of parent class
      this.data = data;
   endfunction

	function display();
      super.display();
      $display ("[Child] addr=0x%0h data=0x%0h", addr, data);
	endfunction
endclass

module tb;
	Packet      bc; 	// bc stands for BaseClass
	ExtPacket   sc; 	// sc stands for SubClass

	initial begin
		bc = new(32'hface_cafe);
		bc.display ();

    sc = new(32'hfeed_feed, 32'h1234_5678);
		sc.display ();
	end
endmodule

//simulation result:
//[Base] addr=0xface_cafe

//[Base] addr=0xfeed_feed
//[Child] addr=0x1234_5678
```

- Abstraction and Polymorphism

```verilog
class Packet;
    int addr;

    function new(int addr);
        this.addr = addr;
    endfunction

    // Without virtual, this won't be polymorphic
    virtual function void display();
        $display("[Base] addr=0x%0h", addr);
    endfunction
endclass

class ExtPacket extends Packet;
    int data;

    function new(int addr, int data);
        super.new(addr);
        this.data = data;
    endfunction

    // Override display
    function void display();
        $display("[Child] addr=0x%0h data=0x%0h", addr, data);
    endfunction
endclass

module tb;
    Packet base_handle;
    ExtPacket child_obj;

    initial begin
        // Create child object, assign to base class handle
        base_handle = new(32'hABCD_EF01);
        base_handle.display(); // Calls base version

        child_obj = new(32'h1234_5678, 32'hDEAD_BEEF);
        child_obj.display();
        
        base_handle = child_obj; // Still pointing to child object
        base_handle.display(); // If 'display' is virtual, calls child version
    end
endmodule

//simulation result:
//[Base] addr=0xABCD_EF01

//[Child] addr=0x1234_5678 data=0xDEAD_BEEF

//If 'display' is virtual, calls child version
//[Child] addr=0x1234_5678 data=0xDEAD_BEEF

//If 'display' is not virtual, calls child version
//[Base] addr=0x1234_5678
```

1. VPI, VHPI, FLI, GPI
- GPI: written in C++, an abstraction layer for VPI, VHPI and FLI.
    - VPI(**Verilog Procedural Interface):** It allows behavioral Verilog code to invoke C functions, and C functions to invoke standard Verilog system tasks.
    - VHPI(**VHDL Procedural Interface)**:  It allows behavioral Verilog code to invoke C functions, and C functions to invoke standard VHDL system tasks.
    - FLI(Foreign language interface): C programming language functions that provide procedural access to information within Model Technology's HDL simulator.

1. cocotb

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer

# Clock generator coroutine
async def clock_gen(signal, period_ns=10):
    """Toggle the clock every half period (simulate a square wave)"""
    while True:
        signal.value = 0
        await Timer(period_ns // 2, units="ns")
        signal.value = 1
        await Timer(period_ns // 2, units="ns")

# Main test coroutine
@cocotb.test()
async def my_test(dut):
    """Test with clock and stimulus in parallel"""

    # Start the clock generator coroutine (runs in background)
    cocotb.start_soon(clock_gen(dut.clk))

    # Reset sequence
    dut.rst.value = 1
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst.value = 0

    # Apply stimulus
    dut.a.value = 1
    await RisingEdge(dut.clk)

    dut.a.value = 0
    await RisingEdge(dut.clk)

    # Read output (example)
    b_val = dut.b.value
    dut._log.info(f"Output b = {b_val}")
```

1. Random Stability
- Once a random variable is assigned a value, it should not change unless explicitly re-randomized.
- Random stability ensures that a random test run produces the same results when rerun with the same seed.

1. What are common types of functional coverage metrics?
- coverpoint

```verilog
coverpoint opcode;
//This checks if all possible opcode values were seen during simulation.
```

- Cross Coverage

```verilog
coverpoint addr;
coverpoint burst_length;

cross addr, burst_length;
//This tracks combinations of addr and burst_length — useful in bus protocol testing.
```

- Transition Coverage

```verilog
coverpoint state {
  bins idle_to_run = (IDLE => RUN);
  bins run_to_done = (RUN => DONE);
}
```

1. Explain the use of callbacks in UVM.
- a powerful mechanism that allows you to **insert custom behavior into standard components** **without modifying their original source code**

1. Discuss the concept of directed testing versus constrained-random testing.

| Aspect | Directed Testing | Constrained-Random Testing |
| --- | --- | --- |
| Definition | Manually written test cases for specific scenarios | randomization + constraints |
| Control | High | Low – relies on randomness |
| Debuggability | Easy to debug | Harder to debug |
| Coverage | Targeted scenarios | a wide range of legal inputs |
| Reusability | Low | High |
| Effort | High effort for complex designs or corner cases | High up-front effort |

1. What is regression testing in the context of verification?
- Regression testing involves re-running a comprehensive set of test cases on the design after any modification or update. It ensures that the changes do not introduce new bugs and that previously working functionality still works.

1. What is the difference between black-box and white-box verification?
- Black-box Verification: Verifies the DUT based on its external behavior **without knowledge of its internal structure**
- White-box Verification: Verifies the DUT **with full knowledge** of its internal structure and implementation, allowing for more detailed testing

1. What is test case prioritization, and why is it important?
- Test case prioritization involves selecting and executing the most critical or risky test cases first to maximize fault detection early in the verification cycle. It helps catch major issues faster and improves the efficiency of the verification process.
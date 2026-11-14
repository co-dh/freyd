import LeetQ.Rel.Lang.Embed
import LeetQ.Rel.Lang.Eval

/-! # Job-shop scheduling (AIMA §6.1.2)

The car assembly: 15 jobs, each a start time in 0…30; a solution is a map s : Job ⟶ N no two of whose
assignments are related by bad, the union of the violated binary constraints as one relation on (job, start). -/

namespace LeetQ.Rel.Programs

rel_program jobshop after prelude where
    obj Job = {AxleF,AxleB,WheelRF,WheelLF,WheelRB,WheelLB,NutsRF,NutsLF,NutsRB,NutsLB,CapRF,CapLF,CapRB,CapLB,Inspect}
    obj N = 0…30                                  -- start times; plus has no value past 30, so 30 is the deadline

    /- The data: durations, precedence, the one tool the two axles share. -/

    dur : Job ⟶ N ≜ {(AxleF,10),(AxleB,10),(WheelRF,1),(WheelLF,1),(WheelRB,1),(WheelLB,1),(NutsRF,2),(NutsLF,2),(NutsRB,2),(NutsLB,2),(CapRF,1),(CapLF,1),(CapRB,1),(CapLB,1),(Inspect,3)}
    pre₀ : Job ⟶ Job ≜ {(AxleF,WheelRF),(AxleF,WheelLF),(AxleB,WheelRB),(AxleB,WheelLB),(WheelRF,NutsRF),(WheelLF,NutsLF),(WheelRB,NutsRB),(WheelLB,NutsLB),(NutsRF,CapRF),(NutsLF,CapLF),(NutsRB,CapRB),(NutsLB,CapLB)}
    pre : Job ⟶ Job ≜ pre₀ ∪ (⊤{(Inspect,Inspect)} − 𝟙)        -- Inspect comes after every other job
    tool : Job ⟶ Job ≜ {(AxleF,AxleB)}                          -- the two axles share one tool

    /- The constraints as one relation on assignments (job, start). -/

    fin : Job×N ⟶ N ≜ ⟨π₁dur,π₂⟩plus             -- the finish time m + d(x)
    bef : Job×N ⟶ Job×N ≜ fin ≤ π₂°               -- (x,m) finishes before (y,n) starts
    bad : Job×N ⟶ Job×N ≜ (π₁ pre π₁° − bef) ∪ (π₁(tool ∪ tool°)π₁° − bef − bef°)   -- two assignments that conflict

    /- The solver: place the jobs in declaration order, each at its earliest start that conflicts with no placed one. -/

    cand : [Job×N]×Job ⟶ N ≜ (π₂⟨𝟙,⊤(Job,N)⟩ − (π₁ ∋ bad))dom(fin)π₂   -- the starts of the job that conflict with no placed one
    step : [Job×N]×Job ⟶ [Job×N] ≜ ⟨π₁,⟨π₂,Λ(cand)est(≤)⟩⟩snoc    -- place the job at its earliest such start
    jobs : 1 ⟶ [Job] ≜ Λ(⊤(1,Job))                              -- the jobs in declaration order
    sched : 1 ⟶ [Job×N] ≜ ⟨nil,jobs⟩loop(step)
    s : Job ⟶ N ≜ π₁° ran(sched ∋) π₂

    check 𝟙(Job) ⊑ s s°                          -- s is entire
    check s° s ⊑ 𝟙(N)                            -- s is simple
    check jobs ⊑ jobs ordered(∼pre°)             -- the declaration order is topological
    check ⟨𝟙,s⟩ bad ⟨𝟙,s⟩° = 𝟘                   -- no two assignments of s conflict
    check s = {(AxleF,0),(AxleB,10),(WheelRF,10),(WheelLF,10),(WheelRB,20),(WheelLB,20),(NutsRF,11),(NutsLF,11),(NutsRB,21),(NutsLB,21),(CapRF,13),(CapLF,13),(CapRB,23),(CapLB,23),(Inspect,24)}

#guard (Lang.runProgram jobshop).isOk

end LeetQ.Rel.Programs

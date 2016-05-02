let nextProofStepId = 0
let nextProofStepUiId = 1

export const addGiven = (formula) => (
  {
    type: 'ADD_GIVEN',
    id: nextProofStepId++,
    uiId: nextProofStepUiId++,
    formula
  }
)

let nextToShowId = 0
let nextToShowUiId = 945 // small alpha

export const addToShow = (formula) => (
  {
    type: 'ADD_TO_SHOW',
    id: nextToShowId++,
    uiId: String.fromCharCode(nextToShowUiId++),
    formula
  }
)

export const addProofStep = (formula, justifications) => (
  {
    type: 'ADD_PROOF_STEP',
    id: nextProofStepId++,
    uiId: nextProofStepUiId++,
    formula,
    justifications
  }
)


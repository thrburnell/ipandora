import fetch from 'isomorphic-fetch'

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

export const selectFormulaAsJustification = (id) => (
  {
    type: 'SELECT_JUSTIFICATION',
    id
  }
)

export const checkProofStep = (formula, justification) => {
  return (dispatch, getState) => {

    const known = getState().knownFormulas
    const jFormulas = justification.map((id) => known[id].formula)

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        goal: formula,
        assumptions: jFormulas
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveCheckStatus(formula, justification, json.validityPreserved))
      })
      .catch((err) => {
        console.log(err)
      })
  }
}

export const receiveCheckStatus = (formula, justification, valid) => (
  {
    type: 'RECEIVE_CHECK_STATUS',
    id: nextProofStepId++,
    uiId: nextProofStepUiId++,
    formula,
    justification,
    valid
  }
)


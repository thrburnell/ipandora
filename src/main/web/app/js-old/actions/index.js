import fetch from 'isomorphic-fetch'

let nextProofStepId = 0
const proofStepUiId = (id) => id + 1

export const addGiven = (formula) => {
  const id = nextProofStepId++
  const uiId = proofStepUiId(id)

  return {
    type: 'ADD_GIVEN',
    id,
    uiId,
    formula
  }
}

let nextToShowId = 0
const toShowUiId = (id) => id + 945 // small alpha

export const addToShow = (formula) => {
  const id = nextToShowId++
  const uiId = String.fromCharCode(toShowUiId(id))
  return {
    type: 'ADD_TO_SHOW',
    id,
    uiId,
    formula
  }
}

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
        method: "LOGICAL_IMPLICATION",
        goal: formula,
        assumptions: jFormulas
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveCheckStatus(formula, justification, json.valid))
      })
      .catch(err => {
        console.log(err)
      })
  }
}

export const receiveCheckStatus = (formula, justification, valid) => {
  const id = nextProofStepId++
  const uiId = proofStepUiId(id)

  return {
    type: 'RECEIVE_CHECK_STATUS',
    id,
    uiId,
    formula,
    justification,
    valid
  }
}

export const uploadProofStructure = (file) => {
  return (dispatch, getState) => {

    const formData = new FormData()
    formData.append("file", file)

    const request = new Request('/api/predicate/read', {
      method: 'post',
      body: formData
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        json.given.map(g => dispatch(addGiven(g)))
        json.toShow.map(ts => dispatch(addToShow(ts)))
      })
      .catch(err => {
        console.log(err)
      })
  }
}

export const clearProof = () => {
  nextProofStepId = 0
  nextToShowId = 0

  return {
    type: 'CLEAR_PROOF'
  }
}

